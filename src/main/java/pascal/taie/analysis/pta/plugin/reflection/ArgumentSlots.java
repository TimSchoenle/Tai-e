/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.plugin.reflection;

import org.jspecify.annotations.Nullable;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ClassLiteral;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.InvokeDynamic;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Literal;
import pascal.taie.ir.exp.NewArray;
import pascal.taie.ir.exp.NullLiteral;
import pascal.taie.ir.exp.StringLiteral;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.ExceptionEntry;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.JumpStmt;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.language.classes.ClassNames;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;

import java.util.List;
import java.util.Set;

/**
 * What each element of the argument array of one reflective call holds
 * when the call runs, found by an intra-procedural look at the code that
 * builds the array, and which parameter types those elements rule out.
 * <p>
 * The look succeeds only for the shape javac emits for
 * {@code m.invoke(r, a, b)} and {@code new Object[]{a, b}}: the array
 * variable has exactly one definition {@code new T[c]} with a constant
 * {@code c}, every other use of the variable is the base of an array store
 * (it is never copied, passed or stored, so no other code can reach the
 * array), it is used once by the call, and no jump or exception handler
 * targets a statement after the definition up to the call. Every path to
 * the call then runs the definition and each statement after it in order,
 * so the array the call gets is the one that definition created, and its
 * element {@code i} is the value of the last store to the constant index
 * {@code i} in that straight run, or {@code null} without one.
 * <p>
 * What an element rules out depends only on the code, never on points-to
 * sets: values the analysis does not model (the box of a primitive that
 * reflection returns, an object a native method makes) would be missing
 * from a points-to set, and ruling a target out on that absence would drop
 * a target the JVM runs.
 */
final class ArgumentSlots {

    /** The classes whose objects {@code invoke} unboxes into a primitive parameter. */
    private static final Set<String> BOXES = Set.of(
            ClassNames.BOOLEAN, ClassNames.BYTE, ClassNames.SHORT, ClassNames.CHARACTER,
            ClassNames.INTEGER, ClassNames.LONG, ClassNames.FLOAT, ClassNames.DOUBLE);

    /** The classes that are supertypes of a box class. */
    private static final Set<String> BOX_SUPERCLASSES = Set.of(
            ClassNames.OBJECT, "java.lang.Number");

    private static final String LAMBDA_META_FACTORY = "java.lang.invoke.LambdaMetafactory";

    private final List<Slot> slots;

    private ArgumentSlots(List<Slot> slots) {
        this.slots = slots;
    }

    /**
     * @return the elements of argument array {@code args} of {@code call},
     * or {@code null} when the look does not find each of them
     */
    static @Nullable ArgumentSlots of(Invoke call, Var args) {
        IR ir = call.getContainer().getIR();
        if (args.isConst() || ir.isParam(args) || args.equals(ir.getThis())) {
            return null;
        }
        New def = null;
        for (Stmt stmt : ir.getStmts()) {
            if (stmt.getDef().filter(args::equals).isPresent()) {
                if (def != null || !(stmt instanceof New newStmt)
                        || !(newStmt.getRValue() instanceof NewArray)) {
                    return null;
                }
                def = newStmt;
            } else if (stmt.getUses().contains(args) && !isAllowedUse(stmt, call, args)) {
                return null;
            }
        }
        if (def == null || !(def.getRValue() instanceof NewArray newArray)) {
            return null;
        }
        int length = constantInt(newArray.getLength());
        int from = def.getIndex();
        int to = call.getIndex();
        if (length < 0 || from >= to || isEnteredBetween(ir, from, to)) {
            return null;
        }
        Var[] stored = new Var[length];
        List<Stmt> stmts = ir.getStmts();
        for (int i = from + 1; i < to; ++i) {
            if (stmts.get(i) instanceof StoreArray store
                    && store.getArrayAccess().getBase().equals(args)) {
                int index = constantInt(store.getArrayAccess().getIndex());
                if (index < 0 || index >= length) {
                    return null;
                }
                stored[index] = store.getRValue();
            }
        }
        Slot[] slots = new Slot[length];
        for (int i = 0; i < length; ++i) {
            slots[i] = stored[i] == null ? NullSlot.INSTANCE : slotOf(ir, stored[i]);
        }
        return new ArgumentSlots(List.of(slots));
    }

    int size() {
        return slots.size();
    }

    /**
     * @return whether element {@code i} can be passed to a parameter of
     * {@code paramType}: {@code invoke} and {@code newInstance} throw
     * {@code IllegalArgumentException} for an element of another type
     * before they call the target, and for {@code null} to a primitive
     * parameter.
     */
    boolean admits(int i, Type paramType, TypeSystem typeSystem) {
        return slots.get(i).admits(paramType, typeSystem);
    }

    /**
     * @return whether {@code stmt}, a use of {@code args}, keeps the array
     * out of reach of other code: an array store with {@code args} as its
     * base only, or {@code call} using it once, as its argument array.
     */
    private static boolean isAllowedUse(Stmt stmt, Invoke call, Var args) {
        if (stmt instanceof StoreArray store) {
            return store.getArrayAccess().getBase().equals(args)
                    && !store.getArrayAccess().getIndex().equals(args)
                    && !store.getRValue().equals(args);
        }
        if (stmt != call) {
            return false;
        }
        InvokeExp exp = call.getInvokeExp();
        int uses = exp instanceof InvokeInstanceExp instanceExp
                && instanceExp.getBase().equals(args) ? 1 : 0;
        for (Var arg : exp.getArgs()) {
            if (arg.equals(args)) {
                ++uses;
            }
        }
        return uses == 1;
    }

    /**
     * @return whether a jump or an exception handler targets a statement
     * with an index in {@code (from, to]}
     */
    private static boolean isEnteredBetween(IR ir, int from, int to) {
        for (Stmt stmt : ir.getStmts()) {
            if (stmt instanceof JumpStmt jump) {
                for (Stmt target : jump.getTargets()) {
                    if (target.getIndex() > from && target.getIndex() <= to) {
                        return true;
                    }
                }
            }
        }
        for (ExceptionEntry entry : ir.getExceptionEntries()) {
            int handler = entry.handler().getIndex();
            if (handler > from && handler <= to) {
                return true;
            }
        }
        return false;
    }

    /**
     * @return the value of int constant {@code var}, or {@code -1} if it is
     * not one
     */
    private static int constantInt(Var var) {
        return var.isConst() && var.getConstValue() instanceof IntLiteral literal
                ? literal.getValue() : -1;
    }

    /**
     * The element a store of {@code value} leaves: {@code null} for the
     * {@code null} constant, an object of a known class for a string or
     * class constant, and, when {@code value} is not a parameter and has
     * exactly one definition, for a definition that cannot yield
     * {@code null} (a {@code new}, a lambda meta factory call). Else (and
     * for {@code this}, which may be of a subclass) a value of the static
     * type of {@code value} or {@code null}.
     */
    private static Slot slotOf(IR ir, Var value) {
        if (value.equals(ir.getThis())) {
            // this is never null; its class may be any subclass
            return new TypedSlot(value.getType());
        }
        if (value.isConst()) {
            // the IR's null constant has no definition statement
            Literal literal = value.getConstValue();
            if (literal instanceof NullLiteral) {
                return NullSlot.INSTANCE;
            }
            if (literal instanceof StringLiteral || literal instanceof ClassLiteral) {
                return new ExactSlot(literal.getType());
            }
            return new TypedSlot(value.getType());
        }
        Stmt def = null;
        if (!ir.isParam(value)) {
            for (Stmt stmt : ir.getStmts()) {
                if (stmt.getDef().filter(value::equals).isPresent()) {
                    if (def != null) {
                        return new TypedSlot(value.getType());
                    }
                    def = stmt;
                }
            }
        }
        if (def instanceof New newStmt) {
            return new ExactSlot(newStmt.getRValue().getType());
        }
        if (def instanceof Invoke invoke
                && invoke.getInvokeExp() instanceof InvokeDynamic indy) {
            MethodRef bootstrap = indy.getBootstrapMethodRef();
            if (LAMBDA_META_FACTORY.equals(bootstrap.getDeclaringClass().getName())) {
                Type iface = indy.getMethodType().getReturnType();
                return switch (bootstrap.getName()) {
                    case "metafactory" -> new LambdaSlot(iface, true);
                    case "altMetafactory" -> new LambdaSlot(iface, false);
                    default -> new TypedSlot(value.getType());
                };
            }
        }
        return new TypedSlot(value.getType());
    }

    private static boolean isBox(Type type) {
        return type instanceof ClassType classType && BOXES.contains(classType.getName());
    }

    /**
     * What one element of the argument array holds when the call runs.
     */
    private sealed interface Slot permits NullSlot, ExactSlot, LambdaSlot, TypedSlot {

        boolean admits(Type paramType, TypeSystem typeSystem);
    }

    /** No store: the element is {@code null}. */
    private enum NullSlot implements Slot {
        INSTANCE;

        @Override
        public boolean admits(Type paramType, TypeSystem typeSystem) {
            return !(paramType instanceof PrimitiveType);
        }
    }

    /** An object of exactly {@code type}, never {@code null}. */
    private record ExactSlot(Type type) implements Slot {

        @Override
        public boolean admits(Type paramType, TypeSystem typeSystem) {
            if (paramType instanceof PrimitiveType) {
                // any box: invoke unboxes, then widens
                return isBox(type);
            }
            return typeSystem.isSubtype(paramType, type);
        }
    }

    /**
     * A lambda object of a class the meta factory spins: it extends
     * {@code Object} and implements {@code iface}; {@code altMetafactory}
     * may add marker interfaces and {@code Serializable}, so then any
     * interface is possible. Never {@code null}.
     */
    private record LambdaSlot(Type iface, boolean onlyIface) implements Slot {

        @Override
        public boolean admits(Type paramType, TypeSystem typeSystem) {
            if (paramType instanceof PrimitiveType) {
                return false;
            }
            if (typeSystem.isSubtype(paramType, iface)
                    || paramType instanceof ClassType classType
                    && ClassNames.OBJECT.equals(classType.getName())) {
                return true;
            }
            return !onlyIface && paramType instanceof ClassType classType
                    && (classType.getJClass() == null || classType.getJClass().isInterface());
        }
    }

    /**
     * {@code null} or an object of any subtype of static type {@code type}:
     * any reference parameter admits it. A primitive parameter admits it
     * unless {@code type} is a class that no box class extends, or an array
     * type: the verifier guarantees a value of a class type is an instance
     * of that class (not so for an interface type).
     */
    private record TypedSlot(Type type) implements Slot {

        @Override
        public boolean admits(Type paramType, TypeSystem typeSystem) {
            if (!(paramType instanceof PrimitiveType)) {
                return true;
            }
            if (type instanceof ArrayType) {
                return false;
            }
            if (type instanceof ClassType classType) {
                JClass jclass = classType.getJClass();
                return jclass == null || jclass.isInterface()
                        || isBox(type) || BOX_SUPERCLASSES.contains(classType.getName());
            }
            return true;
        }
    }
}
