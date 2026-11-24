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

package pascal.taie.analysis.pta.core.cs.selector;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.language.classes.JMethod;

import java.util.concurrent.atomic.AtomicLong;

/**
 * Object sensitivity ({@link KObjSelector}, option {@code cs:k-counting})
 * that counts its instance context selections and declares its instance
 * contexts call-site free only while {@link #callSiteFree} is set, so a
 * test can run one analysis with and without the call-site-free sharing.
 */
public class KCountingSelector implements ContextSelector {

    /**
     * The instance context selections since the last reset.
     */
    public static final AtomicLong INSTANCE_SELECTIONS = new AtomicLong();

    /**
     * The value of {@link #isInstanceContextCallSiteFree()} of the selectors
     * created after it is set.
     */
    public static volatile boolean callSiteFree;

    private final ContextSelector delegate;

    private final boolean free;

    public KCountingSelector(int k, int hk) {
        this.delegate = new KObjSelector(k, hk);
        this.free = callSiteFree;
    }

    @Override
    public Context getEmptyContext() {
        return delegate.getEmptyContext();
    }

    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        return delegate.selectContext(callSite, callee);
    }

    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        INSTANCE_SELECTIONS.incrementAndGet();
        return delegate.selectContext(callSite, recv, callee);
    }

    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        return delegate.selectHeapContext(method, obj);
    }

    @Override
    public boolean isInstanceContextCallSiteFree() {
        return free;
    }
}
