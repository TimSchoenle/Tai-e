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
import pascal.taie.util.collection.Maps;

import java.util.Map;

/**
 * Rules out reflective targets by the number of arguments a reflective
 * call passes, when an intra-procedural look at the call's argument array
 * finds it. This class supports the following reflection APIs:
 * <ul>
 *     <li>Class.newInstance()</li>
 *     <li>Constructor.newInstance(Object[])</li>
 *     <li>Method.invoke(Object,Object[])</li>
 * </ul>
 * The count is the only sound filter: {@code Method.invoke} and
 * {@code Constructor.newInstance} refuse an argument array of another
 * length before they call the target. A cast of the result runs only after
 * the target has returned, and {@code invoke} converts every argument by its
 * runtime object (unboxing, widening), so neither the cast type nor the
 * declared type of a stored argument can rule out a target that runs. The
 * upstream matcher used both and dropped such targets (px/s115-rmp).
 */
class TypeMatcher {

    /** The count of an argument array the look cannot find. */
    private static final int UNKNOWN = -1;

    private static final Map<String, Integer> argIndexes = Map.of(
            "invoke", 1, // Method.invoke(Object,Object[])
            "newInstance", 0 // Constructor.newInstance(Object[])
    );

    private final Map<Invoke, Integer> argCounts = Maps.newMap();

    /**
     * @return whether {@code target} cannot be the target of reflective
     * call {@code invoke}: the call passes a known number of arguments that
     * differs from the target's parameter count.
     */
    boolean isUnmatched(Invoke invoke, JMethod target) {
        int count = getArgCount(invoke);
        return count != UNKNOWN && count != target.getParamCount();
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
        int argIndex = argIndexes.get(invoke.getMethodRef().getName());
        Var args = invoke.getInvokeExp().getArg(argIndex);
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
