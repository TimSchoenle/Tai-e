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

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.language.classes.JMethod;

import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which selectors report the instance context of a call site and callee
 * independent of the receiver object
 * ({@link ContextSelector#isInstanceContextReceiverFree}): those whose
 * instance context does not read the receiver object. The solves of
 * {@code CallBatchingEquivalenceTest} with {@code call-batching: verify}
 * check each such report against the per-object selection.
 */
class ReceiverFreeSelectorTest {

    @ParameterizedTest
    @ValueSource(strings = {"ci", "1-call", "2-call"})
    void selectorsNotReadingTheReceiverAreReceiverFree(String cs) {
        assertTrue(ContextSelectorFactory.makePlainSelector(cs)
                .isInstanceContextReceiverFree(null, null));
    }

    @ParameterizedTest
    @ValueSource(strings = {"1-obj", "2-obj", "1-type", "2-type"})
    void receiverBasedSelectorsAreNot(String cs) {
        assertFalse(ContextSelectorFactory.makePlainSelector(cs)
                .isInstanceContextReceiverFree(null, null));
    }

    @Test
    void theDefaultIsNotReceiverFree() {
        ContextSelector minimal = new ContextSelector() {
            @Override
            public Context getEmptyContext() {
                throw new UnsupportedOperationException();
            }

            @Override
            public Context selectContext(CSCallSite callSite, JMethod callee) {
                throw new UnsupportedOperationException();
            }

            @Override
            public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
                throw new UnsupportedOperationException();
            }

            @Override
            public Context selectHeapContext(CSMethod method, Obj obj) {
                throw new UnsupportedOperationException();
            }
        };
        assertFalse(minimal.isInstanceContextReceiverFree(null, null));
    }

    @Test
    void selectiveSelectorIsReceiverFreeOutsideItsMethods() {
        assertTrue(ContextSelectorFactory.makeSelectiveSelector(
                "1-obj", m -> false, o -> true).isInstanceContextReceiverFree(null, null));
        assertFalse(ContextSelectorFactory.makeSelectiveSelector(
                "1-obj", m -> true, o -> true).isInstanceContextReceiverFree(null, null));
        assertTrue(ContextSelectorFactory.makeSelectiveSelector(
                "1-call", m -> true, o -> true).isInstanceContextReceiverFree(null, null));
    }

    @Test
    void guidedSelectorIsReceiverFreeForCiOnly() {
        Map<JMethod, String> csMap = new HashMap<>();
        assertTrue(new GuidedSelector(csMap).isInstanceContextReceiverFree(null, null),
                "an unlisted method gets ci");
        for (String cs : new String[]{"1-type", "2-type", "2-obj"}) {
            csMap.put(null, cs);
            assertFalse(new GuidedSelector(csMap).isInstanceContextReceiverFree(null, null), cs);
        }
        csMap.put(null, "ci");
        assertTrue(new GuidedSelector(csMap).isInstanceContextReceiverFree(null, null));
    }
}
