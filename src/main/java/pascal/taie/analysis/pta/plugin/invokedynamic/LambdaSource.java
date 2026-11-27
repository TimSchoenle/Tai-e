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
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.ir.exp.InvokeDynamic;
import pascal.taie.util.Hashes;

import java.util.List;
import java.util.Objects;

/**
 * The invokedynamic that created a lambda functional object and the context
 * under which the lambda call edges on that object read its captured
 * variables: what a {@link LambdaCallEdge} carries beyond its call site and
 * callee. {@link LambdaAnalysis} interns one source per pair, so the call
 * sites and callees hold each lambda call edge as this shared source.
 * <p>
 * A call can also reach a lambda object as the receiver of a method
 * reference whose target is the lambda's functional method (a bound
 * {@code r1::run}, or an unbound {@code Runnable::run} applied to the lambda
 * object {@code r1}). The source of such an edge also holds the
 * {@link #getSamArgs() arguments} of that call of the functional method, the
 * ones the method reference passes to its target, which the edge passes
 * instead of the call site's.
 */
final class LambdaSource implements LambdaEdgeSource {

    private final InvokeDynamic indy;

    private final Context context;

    @Nullable
    private final List<CSVar> samArgs;

    /**
     * Cache of the interned shape {@link LambdaAnalysis} gives this source
     * under the option {@code lambda-shared-edges}; not part of the identity.
     */
    @Nullable
    private LambdaShape shape;

    LambdaSource(InvokeDynamic indy, Context context) {
        this(indy, context, null);
    }

    LambdaSource(InvokeDynamic indy, Context context, @Nullable List<CSVar> samArgs) {
        this.indy = indy;
        this.context = context;
        this.samArgs = samArgs == null ? null : List.copyOf(samArgs);
    }

    InvokeDynamic getIndy() {
        return indy;
    }

    Context getContext() {
        return context;
    }

    /**
     * @return the arguments of the call of the functional method of this
     * source's lambda objects, when a method reference whose receiver they
     * are makes that call; null if the call site calls them directly (the
     * arguments are then the call site's).
     */
    @Nullable
    @Override
    public List<CSVar> getSamArgs() {
        return samArgs;
    }

    @Override
    public int capturedCount() {
        return indy.getArgs().size();
    }

    @Nullable
    LambdaShape getShape() {
        return shape;
    }

    void setShape(LambdaShape shape) {
        this.shape = shape;
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
    @Override
    public int edgeHashCode(int edgeHash) {
        int result = edgeHash;
        result = 31 * result + indy.hashCode();
        result = 31 * result + context.hashCode();
        if (samArgs != null) {
            result = 31 * result + samArgs.hashCode();
        }
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
        return indy.equals(that.indy) && context.equals(that.context)
                && Objects.equals(samArgs, that.samArgs);
    }

    @Override
    public int hashCode() {
        return samArgs == null
                ? Hashes.hash(indy, context)
                : Hashes.hash(indy, context, samArgs);
    }

    @Override
    public String toString() {
        return samArgs == null
                ? context + ":" + indy
                : context + ":" + indy + " with " + samArgs;
    }
}
