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

package pascal.taie.analysis.pta.core.solver;

import org.jspecify.annotations.Nullable;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.NullLiteral;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Return;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ReferenceType;

import java.util.List;

/**
 * The shape of a trivial getter, for option {@code trivial-getters}
 * (px/s115-P57): a method without parameters that returns a reference and
 * whose IR is exactly one of
 * <ul>
 *     <li>{@code t = this.f; return t;} ({@link Form#INSTANCE_FIELD},
 *     an instance method),</li>
 *     <li>{@code t = C.f; return t;} ({@link Form#STATIC_FIELD}),</li>
 *     <li>{@code return $null;}, where {@code $null} is the IR's constant
 *     variable of {@code null} ({@link Form#NULL}).</li>
 * </ul>
 * Every other method has the form {@link Form#NONE}.
 *
 * @param form the form of the method
 * @param load the load of an instance or static field form, otherwise null
 */
record TrivialGetter(Form form, @Nullable LoadField load) {

    enum Form {
        /** Not a trivial getter. */
        NONE,
        /** Returns an instance field of {@code this}. */
        INSTANCE_FIELD,
        /** Returns a static field. */
        STATIC_FIELD,
        /** Returns {@code null}. */
        NULL,
    }

    private static final TrivialGetter NOT_TRIVIAL = new TrivialGetter(Form.NONE, null);

    private static final TrivialGetter RETURNS_NULL = new TrivialGetter(Form.NULL, null);

    /**
     * @return the shape of the method, {@link Form#NONE} when it is not a
     * trivial getter
     */
    static TrivialGetter of(JMethod method) {
        if (method.isAbstract() || method.isNative()
                || method.getParamCount() != 0
                || !(method.getReturnType() instanceof ReferenceType)) {
            return NOT_TRIVIAL;
        }
        IR ir = method.getIR();
        List<Stmt> stmts = ir.getStmts();
        if (stmts.isEmpty() || !(stmts.get(stmts.size() - 1) instanceof Return ret)
                || ret.getValue() == null) {
            return NOT_TRIVIAL;
        }
        Var result = ret.getValue();
        if (stmts.size() == 1) {
            return result.isConst() && result.getConstValue() instanceof NullLiteral
                    ? RETURNS_NULL : NOT_TRIVIAL;
        }
        if (stmts.size() != 2) {
            return NOT_TRIVIAL;
        }
        if (stmts.get(0) instanceof LoadField load && load.getLValue() == result) {
            if (load.isStatic()) {
                return new TrivialGetter(Form.STATIC_FIELD, load);
            }
            if (!method.isStatic()
                    && ((InstanceFieldAccess) load.getFieldAccess()).getBase() == ir.getThis()) {
                return new TrivialGetter(Form.INSTANCE_FIELD, load);
            }
        }
        return NOT_TRIVIAL;
    }
}
