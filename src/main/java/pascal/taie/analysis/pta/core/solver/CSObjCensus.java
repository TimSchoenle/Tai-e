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

import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.heap.ConstantObj;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.NewObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeDynamic;
import pascal.taie.ir.stmt.Invoke;

/**
 * The census of the context-sensitive objects of a {@link CSManager},
 * taken with the solver census: the objects by kind and by whether their
 * heap context is empty, the lambda objects by whether their
 * {@code invokedynamic} captures a variable, and the instance field and
 * array index pointers whose base object is a lambda object.
 *
 * @param byKind          the objects by kind, indexed by the {@code KIND_}
 *                        constants
 * @param emptyContext    the objects of each kind whose heap context is
 *                        empty
 * @param lambdaCapturing the lambda objects whose {@code invokedynamic}
 *                        captures at least one variable
 * @param lambdaFields    the instance field pointers on a lambda object
 * @param lambdaIndexes   the array index pointers on a lambda object
 */
record CSObjCensus(long[] byKind, long[] emptyContext, long lambdaCapturing,
                   long lambdaFields, long lambdaIndexes) {

    /**
     * The descriptor text of the functional objects that the lambda
     * analysis creates at a lambda meta factory call.
     */
    static final String LAMBDA_DESCRIPTOR = "LambdaObj";

    static final int KIND_LAMBDA = 0;

    static final int KIND_NEW = 1;

    static final int KIND_MOCK = 2;

    static final int KIND_CONST = 3;

    static final int KIND_OTHER = 4;

    private static final String[] KIND_NAMES = {"lambda", "new", "mock", "const", "other"};

    /**
     * Counts the objects and pointers of the manager.
     */
    static CSObjCensus take(CSManager csManager) {
        long[] byKind = new long[KIND_NAMES.length];
        long[] emptyContext = new long[KIND_NAMES.length];
        long capturing = 0;
        for (CSObj o : csManager.getObjects()) {
            int kind = kindOf(o.getObject());
            ++byKind[kind];
            if (o.getContext().getLength() == 0) {
                ++emptyContext[kind];
            }
            if (kind == KIND_LAMBDA && capturesVariables((MockObj) o.getObject())) {
                ++capturing;
            }
        }
        long fields = 0;
        for (InstanceField f : csManager.getInstanceFields()) {
            if (isLambda(f.getBase())) {
                ++fields;
            }
        }
        long indexes = 0;
        for (ArrayIndex a : csManager.getArrayIndexes()) {
            if (isLambda(a.getArray())) {
                ++indexes;
            }
        }
        return new CSObjCensus(byKind, emptyContext, capturing, fields, indexes);
    }

    static int kindOf(Obj obj) {
        if (obj instanceof MockObj mock) {
            return mock.getDescriptor().string().equals(LAMBDA_DESCRIPTOR)
                    ? KIND_LAMBDA : KIND_MOCK;
        }
        if (obj instanceof NewObj) {
            return KIND_NEW;
        }
        if (obj instanceof ConstantObj) {
            return KIND_CONST;
        }
        return KIND_OTHER;
    }

    private static boolean isLambda(CSObj o) {
        return kindOf(o.getObject()) == KIND_LAMBDA;
    }

    private static boolean capturesVariables(MockObj lambda) {
        return lambda.getAllocation() instanceof Invoke invoke
                && invoke.getInvokeExp() instanceof InvokeDynamic indy
                && !indy.getArgs().isEmpty();
    }

    @Override
    public String toString() {
        StringBuilder line = new StringBuilder("cs-objects census:");
        for (int i = 0; i < KIND_NAMES.length; ++i) {
            line.append(' ').append(KIND_NAMES[i]).append('=').append(byKind[i])
                    .append("(empty_ctx=").append(emptyContext[i]).append(')');
        }
        return line.append(" lambda_capturing=").append(lambdaCapturing)
                .append(" lambda_noncapturing=").append(byKind[KIND_LAMBDA] - lambdaCapturing)
                .append(" instance_fields_on_lambda=").append(lambdaFields)
                .append(" array_indexes_on_lambda=").append(lambdaIndexes)
                .toString();
    }
}
