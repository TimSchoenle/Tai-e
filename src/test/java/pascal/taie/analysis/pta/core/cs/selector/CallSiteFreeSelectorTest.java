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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which selectors declare their instance contexts call-site free: those
 * whose instance context reads only the receiver object and the callee.
 */
class CallSiteFreeSelectorTest {

    @ParameterizedTest
    @ValueSource(strings = {"ci", "1-obj", "2-obj", "1-type", "2-type"})
    void receiverBasedSelectorsAreCallSiteFree(String cs) {
        assertTrue(ContextSelectorFactory.makePlainSelector(cs)
                .isInstanceContextCallSiteFree());
    }

    @ParameterizedTest
    @ValueSource(strings = {"1-call", "2-call"})
    void callSiteSelectorsAreNot(String cs) {
        assertFalse(ContextSelectorFactory.makePlainSelector(cs)
                .isInstanceContextCallSiteFree());
    }

    @Test
    void selectiveSelectorFollowsItsDelegate() {
        assertTrue(ContextSelectorFactory.makeSelectiveSelector(
                "1-obj", m -> true, o -> true).isInstanceContextCallSiteFree());
        assertFalse(ContextSelectorFactory.makeSelectiveSelector(
                "1-call", m -> true, o -> true).isInstanceContextCallSiteFree());
    }
}
