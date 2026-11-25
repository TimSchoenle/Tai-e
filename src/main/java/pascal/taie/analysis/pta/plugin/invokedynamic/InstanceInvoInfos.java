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

import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.util.Hashes;

/**
 * The lambda instance invocations on one receiver variable: per invocation
 * its context-sensitive call site and the source of its call edges (the
 * invokedynamic that created the lambda objects and the context of their
 * captured variables). The target method reference and the argument counts
 * of an invocation are functions of these two, so they are not stored.
 * Iterates in the order of a hybrid hash set of invocation objects equal by
 * call site and source, hashed by call site, invokedynamic and context.
 */
final class InstanceInvoInfos extends HashOrderPairSet<CSCallSite, LambdaSource> {

    @Override
    protected int hash(CSCallSite csCallSite, LambdaSource source) {
        return Hashes.hash(csCallSite, source.getIndy(), source.getContext());
    }
}
