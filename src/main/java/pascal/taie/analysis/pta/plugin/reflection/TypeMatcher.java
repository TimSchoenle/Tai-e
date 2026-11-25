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
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.NewArray;
import pascal.taie.ir.exp.NullLiteral;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.collection.Maps;

import java.util.Map;
import java.util.Optional;

/**
 * Rules out reflective targets that a reflective call can never run. This
 * class supports the following reflection APIs:
 * <ul>
 *     <li>Class.newInstance()</li>
 *     <li>Constructor.newInstance(Object[])</li>
 *     <li>Method.invoke(Object,Object[])</li>
 * </ul>
 * Each rule is a check the JVM makes before it calls the target:
 * <ul>
 *     <li>the number of arguments, when an intra-procedural look at the
 *     call's argument array finds it: {@code Method.invoke} and
 *     {@code Constructor.newInstance} refuse an argument array of another
 *     length;</li>
 *     <li>the type of each argument, when {@link ArgumentSlots} finds what
 *     each element holds: both refuse an argument the parameter type does
 *     not admit after unboxing, and {@code null} for a primitive
 *     parameter;</li>
 *     <li>a constructor of an abstract class: {@code newInstance} throws
 *     {@code InstantiationException}.</li>
 * </ul>
 * A cast of the result runs only after the target has returned, so it
 * cannot rule out a target that runs; nor can the declared type of a
 * stored argument whose value may be {@code null} or of a subtype. The
 * upstream matcher used both and dropped such targets (px/s115-rmp).
 */
class TypeMatcher {

    /** The count of an argument array the look cannot find. */
    private static final int UNKNOWN = -1;

    private static final Map<String, Integer> argIndexes = Map.of(
            "invoke", 1, // Method.invoke(Object,Object[])
            "newInstance", 0 // Constructor.newInstance(Object[])
    );

    private final TypeSystem typeSystem;

    private final Map<Invoke, Integer> argCounts = Maps.newMap();

    private final Map<Invoke, Optional<ArgumentSlots>> argSlots = Maps.newMap();

    TypeMatcher(TypeSystem typeSystem) {
        this.typeSystem = typeSystem;
    }

    /**
     * @return whether {@code target} cannot be the target of reflective
     * call {@code invoke}: the call passes a known number of arguments that
     * differs from the target's parameter count, an argument the target's
     * parameter does not admit, or {@code target} constructs an abstract
     * class.
     */
    boolean isUnmatched(Invoke invoke, JMethod target) {
        if (target.isConstructor() && target.getDeclaringClass().isAbstract()) {
            return true;
        }
        int count = getArgCount(invoke);
        if (count == UNKNOWN) {
            return false;
        }
        if (count != target.getParamCount()) {
            return true;
        }
        ArgumentSlots slots = getArgSlots(invoke);
        if (slots != null && slots.size() == count) {
            for (int i = 0; i < count; ++i) {
                if (!slots.admits(i, target.getParamType(i), typeSystem)) {
                    return true;
                }
            }
        }
        return false;
    }

    private @Nullable ArgumentSlots getArgSlots(Invoke invoke) {
        return argSlots.computeIfAbsent(invoke, call -> call.getInvokeExp().getArgCount() == 0
                ? Optional.empty()
                : Optional.ofNullable(ArgumentSlots.of(call, getArgsVar(call)))).orElse(null);
    }

    private static Var getArgsVar(Invoke invoke) {
        return invoke.getInvokeExp().getArg(argIndexes.get(invoke.getMethodRef().getName()));
    }

    /**
     * @return whether the number of arguments {@code invoke} passes is known.
     */
    boolean hasTypeInfo(Invoke invoke) {
        return getArgCount(invoke) != UNKNOWN;
    }

    private int getArgCount(Invoke invoke) {
        return argCounts.computeIfAbsent(invoke, TypeMatcher::computeArgCount);
    }

    /**
     * Computes the number of arguments of reflective call {@code invoke}:
     * none for {@code Class.newInstance()} and for a {@code null} argument
     * array; else the length of the array when the array variable has
     * exactly one definition in the whole method, is neither a parameter nor
     * {@code this}, and that definition is {@code new T[c]} with a constant
     * {@code c} or a {@code null}. Every array the variable can hold then has
     * that length, on every path and in every loop iteration. A
     * {@code Catch} defines a variable without being a DefinitionStmt; the
     * scan cannot miss one here, as a caught value is a Throwable and never
     * an argument array.
     */
    private static int computeArgCount(Invoke invoke) {
        if (invoke.getInvokeExp().getArgCount() == 0) {
            // no argument, it means that invoke calls Class.newInstance()
            return 0;
        }
        Var args = getArgsVar(invoke);
        if (args.isConst() && args.getConstValue() instanceof NullLiteral) {
            // a null argument array: no argument is given
            return 0;
        }
        IR ir = invoke.getContainer().getIR();
        if (ir.isParam(args) || args.equals(ir.getThis())) {
            // the value on entry reaches the call too
            return UNKNOWN;
        }
        DefinitionStmt<?, ?> argDef = null;
        for (Stmt stmt : ir.getStmts()) {
            if (stmt instanceof DefinitionStmt<?, ?> defStmt
                    && args.equals(defStmt.getLValue())) {
                if (argDef != null) {
                    // several definitions of args, give up
                    return UNKNOWN;
                }
                argDef = defStmt;
            }
        }
        return argDef == null ? UNKNOWN : getArrayLength(argDef.getRValue());
    }

    /**
     * Given a {@link RValue}, computes the length of the array it corresponds to.
     * @return the array length, or {@link #UNKNOWN} if {@code rValue} does not
     * correspond to an analyzable array.
     */
    private static int getArrayLength(RValue rValue) {
        if (rValue instanceof NewArray newArray) {
            Var length = newArray.getLength();
            if (length.isConst()
                    && length.getConstValue() instanceof IntLiteral intLiteral
                    && intLiteral.getValue() >= 0) {
                // args = new Object[const];
                return intLiteral.getValue();
            }
        }
        if (rValue instanceof NullLiteral) {
            // args = null;
            return 0;
        }
        if (rValue instanceof CastExp castExp
                && castExp.getValue().isConst()
                && castExp.getValue().getConstValue() instanceof NullLiteral) {
            // args = (Object[]) null;
            return 0;
        }
        return UNKNOWN;
    }
}
