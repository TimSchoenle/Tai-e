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

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.ir.exp.InvokeDynamic;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.util.Hashes;

class InstanceInvoInfo {

    private final CSCallSite csCallSite;

    private final InvokeDynamic lambdaIndy;

    private final Context lambdaContext;

    /**
     * The target method reference of the method handle of {@link #lambdaIndy}.
     */
    private final MethodRef targetRef;

    /**
     * Number of arguments a call edge of this invocation transfers into
     * the parameters of a static method or constructor.
     */
    private final int argsToStatic;

    /**
     * Number of arguments a call edge of this invocation transfers into
     * the parameters of an instance method.
     */
    private final int argsToInstance;

    /**
     * The derived fields are functions of {@code csCallSite} and
     * {@code lambdaIndy}, so they take no part in equality.
     */
    InstanceInvoInfo(CSCallSite csCallSite,
                     InvokeDynamic lambdaIndy,
                     Context lambdaContext,
                     MethodRef targetRef,
                     int argsToStatic,
                     int argsToInstance) {
        this.csCallSite = csCallSite;
        this.lambdaIndy = lambdaIndy;
        this.lambdaContext = lambdaContext;
        this.targetRef = targetRef;
        this.argsToStatic = argsToStatic;
        this.argsToInstance = argsToInstance;
    }

    MethodRef getTargetRef() {
        return targetRef;
    }

    int getArgsToStatic() {
        return argsToStatic;
    }

    int getArgsToInstance() {
        return argsToInstance;
    }

    CSCallSite getCSCallSite() {
        return csCallSite;
    }

    InvokeDynamic getLambdaIndy() {
        return lambdaIndy;
    }

    Context getLambdaContext() {
        return lambdaContext;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        InstanceInvoInfo that = (InstanceInvoInfo) o;
        return csCallSite.equals(that.csCallSite) &&
                lambdaIndy.equals(that.lambdaIndy) &&
                lambdaContext.equals(that.lambdaContext);
    }

    @Override
    public int hashCode() {
        return Hashes.hash(csCallSite, lambdaIndy, lambdaContext);
    }
}
