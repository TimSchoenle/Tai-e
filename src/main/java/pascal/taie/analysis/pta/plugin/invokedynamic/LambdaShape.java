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

import org.jspecify.annotations.Nullable;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.util.Hashes;

import java.util.List;
import java.util.Objects;

/**
 * The passing shape of a lambda call edge with the option
 * {@code lambda-shared-edges}: the number of captured variables and the
 * arguments of a method reference's call ({@link LambdaSource#getSamArgs}).
 * The facts a lambda call edge adds from its call site (actual or forwarded
 * arguments to the parameters after the captured ones, callee returns to
 * the call's result) depend on its call site, callee and this shape only, so
 * the edges of one call site and callee from sources of one shape are one
 * edge. {@link LambdaAnalysis} interns one shape per value and passes the
 * captured variables of each source itself, once per source and callee.
 */
final class LambdaShape implements LambdaEdgeSource {

    private final int capturedCount;

    @Nullable
    private final List<CSVar> samArgs;

    /**
     * @param samArgs the arguments of a method reference's call, copied by
     *                the {@link LambdaSource} that gives them
     */
    LambdaShape(int capturedCount, @Nullable List<CSVar> samArgs) {
        this.capturedCount = capturedCount;
        this.samArgs = samArgs;
    }

    @Override
    public int capturedCount() {
        return capturedCount;
    }

    @Nullable
    @Override
    public List<CSVar> getSamArgs() {
        return samArgs;
    }

    @Override
    public Edge<CSCallSite, CSMethod> edge(CSCallSite callSite, CSMethod callee) {
        return new LambdaCallEdge(callSite, callee, this);
    }

    @Override
    public int edgeHashCode(CSCallSite callSite, CSMethod callee) {
        return edgeHashCode(Hashes.hash(CallKind.OTHER, callSite, callee));
    }

    @Override
    public int edgeHashCode(int edgeHash) {
        return 31 * (31 * edgeHash + capturedCount) + Objects.hashCode(samArgs);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        LambdaShape that = (LambdaShape) o;
        return capturedCount == that.capturedCount && Objects.equals(samArgs, that.samArgs);
    }

    @Override
    public int hashCode() {
        return 31 * capturedCount + Objects.hashCode(samArgs);
    }

    @Override
    public String toString() {
        return samArgs == null
                ? "shape(" + capturedCount + ")"
                : "shape(" + capturedCount + ", " + samArgs + ")";
    }
}
