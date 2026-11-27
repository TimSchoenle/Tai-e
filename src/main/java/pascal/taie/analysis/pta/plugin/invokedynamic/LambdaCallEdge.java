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

import pascal.taie.analysis.graph.callgraph.OtherEdge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.SourcedEdge;
import pascal.taie.analysis.pta.core.solver.CallBlockProbe;
import pascal.taie.ir.exp.Var;
import pascal.taie.language.classes.JMethod;

import java.util.List;

/**
 * Represents call edge on lambda functional object.
 * The edge carries the information about invokedynamic invocation site
 * where the lambda functional object was created, as its
 * {@link LambdaSource}; call sites and callees hold the edge as that source
 * and rebuild it on read.
 */
final class LambdaCallEdge extends OtherEdge<CSCallSite, CSMethod>
        implements SourcedEdge, CallBlockProbe.Classified {

    private final LambdaSource source;

    LambdaCallEdge(CSCallSite csCallSite, CSMethod callee, LambdaSource source) {
        super(csCallSite, callee);
        this.source = source;
    }

    @Override
    public CallBlockProbe.EdgeClass blockProbeClass() {
        return probeClass(source, getCallee().getMethod());
    }

    /**
     * @return the block probe's class of a lambda call edge of
     * {@code source} to {@code callee}: a constructor, a static method, an
     * instance method with a captured receiver (bound) or one dispatched on
     * the first argument the call passes (unbound)
     */
    static CallBlockProbe.EdgeClass probeClass(LambdaSource source, JMethod callee) {
        if (callee.isConstructor()) {
            return CallBlockProbe.EdgeClass.LAMBDA_NEW;
        }
        if (callee.isStatic()) {
            return CallBlockProbe.EdgeClass.LAMBDA_STATIC;
        }
        return source.getIndy().getArgs().isEmpty()
                ? CallBlockProbe.EdgeClass.LAMBDA_UNBOUND
                : CallBlockProbe.EdgeClass.LAMBDA_BOUND;
    }

    List<Var> getCapturedArgs() {
        return source.getIndy().getArgs();
    }

    Context getLambdaContext() {
        return source.getContext();
    }

    @Override
    public LambdaSource getSource() {
        return source;
    }

    /**
     * @return true: the call on the functional object runs the lambda body,
     * and what the body throws leaves that call.
     */
    @Override
    public boolean propagatesExceptions() {
        return true;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        if (!super.equals(o)) {
            return false;
        }
        LambdaCallEdge that = (LambdaCallEdge) o;
        return source.equals(that.source);
    }

    @Override
    public int hashCode() {
        return source.edgeHashCode(super.hashCode());
    }
}
