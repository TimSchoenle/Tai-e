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

package pascal.taie.analysis.pta.plugin.invokedynamic;

import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.EdgeSource;
import pascal.taie.ir.exp.InvokeDynamic;
import pascal.taie.util.Hashes;

/**
 * The invokedynamic that created a lambda functional object and the context
 * under which the lambda call edges on that object read its captured
 * variables: what a {@link LambdaCallEdge} carries beyond its call site and
 * callee. {@link LambdaAnalysis} interns one source per pair, so the call
 * sites and callees hold each lambda call edge as this shared source.
 */
final class LambdaSource implements EdgeSource {

    private final InvokeDynamic indy;

    private final Context context;

    LambdaSource(InvokeDynamic indy, Context context) {
        this.indy = indy;
        this.context = context;
    }

    InvokeDynamic getIndy() {
        return indy;
    }

    Context getContext() {
        return context;
    }

    @Override
    public Edge<CSCallSite, CSMethod> edge(CSCallSite callSite, CSMethod callee) {
        return new LambdaCallEdge(callSite, callee, this);
    }

    /**
     * @return the hash code of {@code edge(callSite, callee)}: the
     * {@link Edge} hash code of an {@link CallKind#OTHER} edge from
     * {@code callSite} to {@code callee}, combined by
     * {@link #edgeHashCode(int)}.
     */
    @Override
    public int edgeHashCode(CSCallSite callSite, CSMethod callee) {
        return edgeHashCode(Hashes.hash(CallKind.OTHER, callSite, callee));
    }

    /**
     * @return the hash code of a lambda call edge of this source whose
     * {@link Edge} hash code is {@code edgeHash}.
     */
    int edgeHashCode(int edgeHash) {
        int result = edgeHash;
        result = 31 * result + indy.hashCode();
        result = 31 * result + context.hashCode();
        return result;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        LambdaSource that = (LambdaSource) o;
        return indy.equals(that.indy) && context.equals(that.context);
    }

    @Override
    public int hashCode() {
        return Hashes.hash(indy, context);
    }

    @Override
    public String toString() {
        return context + ":" + indy;
    }
}
