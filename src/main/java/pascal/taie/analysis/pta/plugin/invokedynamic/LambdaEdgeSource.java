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
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.EdgeSource;

import java.util.List;

/**
 * What a {@link LambdaCallEdge} carries beyond its call site and callee:
 * the {@link LambdaSource} that made it, or, with the option
 * {@code lambda-shared-edges}, only its {@link LambdaShape passing shape}.
 * Both give what the edge passes from its call site to the callee (its
 * call-site facts); only a {@link LambdaSource} also gives the captured
 * variables.
 */
sealed interface LambdaEdgeSource extends EdgeSource permits LambdaSource, LambdaShape {

    /**
     * @return the number of variables the lambda captured: the leading
     * parameters (after the receiver, if the first captured variable is it)
     * the call-site arguments come after.
     */
    int capturedCount();

    /**
     * @return the arguments a method reference passes to the lambda's
     * functional method, or null if the call site's own arguments are passed
     * ({@link LambdaSource#getSamArgs}).
     */
    @Nullable
    List<CSVar> getSamArgs();

    /**
     * @return the hash code of a lambda call edge of this source whose
     * {@link pascal.taie.analysis.graph.callgraph.Edge} hash code is
     * {@code edgeHash}.
     */
    int edgeHashCode(int edgeHash);
}
