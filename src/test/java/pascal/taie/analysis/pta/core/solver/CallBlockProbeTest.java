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

package pascal.taie.analysis.pta.core.solver;

import org.junit.jupiter.api.Test;
import pascal.taie.analysis.pta.core.solver.CallBlockProbe.Counter;
import pascal.taie.analysis.pta.core.solver.CallBlockProbe.EdgeClass;
import pascal.taie.config.ConfigException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The counters of {@link CallBlockProbe} on batches with known sharing. A
 * batch is offered as pairs (object index, callee key) at a site.
 */
class CallBlockProbeTest {

    private static final EdgeClass PLAIN = EdgeClass.PLAIN;

    /** Offers {@code pairs} (object, callee, object, callee, ...) as one batch. */
    private static void batch(CallBlockProbe probe, long site, EdgeClass edgeClass,
                              int... pairs) {
        CallBlockProbe.Batch batch = probe.begin(site, edgeClass);
        for (int i = 0; i < pairs.length; i += 2) {
            batch.offer(pairs[i], pairs[i + 1]);
        }
        probe.end(batch);
    }

    @Test
    void twoContextsWithTheSameReceiverSetShareOneBlock() {
        CallBlockProbe probe = new CallBlockProbe(true, null);
        // contexts A and B: receivers 1 -> callee 10, 2 -> callee 20
        batch(probe, 7, PLAIN, 1, 10, 2, 20);
        batch(probe, 7, PLAIN, 2, 20, 1, 10);
        assertEquals(2, probe.count(PLAIN, Counter.BATCHES));
        assertEquals(4, probe.count(PLAIN, Counter.OFFERS));
        assertEquals(4, probe.count(PLAIN, Counter.DIRECT));
        assertEquals(1, probe.count(PLAIN, Counter.P1_BLOCKS));
        assertEquals(1, probe.count(PLAIN, Counter.P1_HITS));
        assertEquals(2, probe.count(PLAIN, Counter.P1_BLOCK_PAIRS));
        assertEquals(2, probe.count(PLAIN, Counter.P1_BLOCK_TARGETS));
        // two hub references plus two target edges
        assertEquals(4, probe.phase1Cost(PLAIN));
        assertEquals(4, probe.phase1RuleCost(PLAIN));
        assertEquals(1, probe.count(PLAIN, Counter.P1B_HITS));
        assertEquals(1 + 2 + 1, probe.count(PLAIN, Counter.P1B_COST));
        // the empty batch counts nothing
        batch(probe, 7, PLAIN);
        assertEquals(2, probe.count(PLAIN, Counter.BATCHES));
    }

    @Test
    void blocksAreKeptPerSiteAndClass() {
        CallBlockProbe probe = new CallBlockProbe(false, null);
        batch(probe, 7, PLAIN, 1, 10, 2, 20);
        batch(probe, 8, PLAIN, 1, 10, 2, 20);
        batch(probe, 7, EdgeClass.LAMBDA_BOUND, 1, 10, 2, 20);
        assertEquals(0, probe.count(PLAIN, Counter.P1_HITS));
        assertEquals(2, probe.count(PLAIN, Counter.P1_BLOCKS));
        assertEquals(1, probe.count(EdgeClass.LAMBDA_BOUND, Counter.P1_BLOCKS));
        // a pair with another callee node is another content
        batch(probe, 7, PLAIN, 1, 10, 2, 21);
        assertEquals(3, probe.count(PLAIN, Counter.P1_BLOCKS));
    }

    @Test
    void aLateJoinerIsCoveredInPhase1b() {
        CallBlockProbe probe = new CallBlockProbe(true, null);
        // context A gets two diffs, context B joins late with their union
        batch(probe, 7, PLAIN, 1, 10, 2, 20);
        batch(probe, 7, PLAIN, 3, 30, 4, 40);
        batch(probe, 7, PLAIN, 1, 10, 2, 20, 3, 30, 4, 40);
        assertEquals(3, probe.count(PLAIN, Counter.P1_BLOCKS));
        assertEquals(0, probe.count(PLAIN, Counter.P1_HITS));
        assertEquals(3 + 2 + 2 + 4, probe.phase1Cost(PLAIN));
        assertEquals(1, probe.count(PLAIN, Counter.P1B_COVERED));
        assertEquals(2, probe.count(PLAIN, Counter.P1B_PIECES));
        assertEquals(2, probe.count(PLAIN, Counter.P1B_BLOCKS));
        // two new blocks (1 + 2 each), then two hub references
        assertEquals(3 + 3 + 2, probe.count(PLAIN, Counter.P1B_COST));
        // a later joiner with one more pair: two pieces and a direct edge
        batch(probe, 7, PLAIN, 1, 10, 2, 20, 3, 30, 4, 40, 5, 50);
        assertEquals(2, probe.count(PLAIN, Counter.P1B_COVERED));
        assertEquals(3 + 3 + 2 + 3, probe.count(PLAIN, Counter.P1B_COST));
        // and one with a remainder of two pairs: a new remainder block
        batch(probe, 7, PLAIN, 1, 10, 2, 20, 6, 60, 7, 70);
        assertEquals(3, probe.count(PLAIN, Counter.P1B_BLOCKS));
        assertEquals(3 + 3 + 2 + 3 + (1 + 1 + 2), probe.count(PLAIN, Counter.P1B_COST));
        assertEquals(0, probe.count(PLAIN, Counter.P1B_FALLBACKS));
    }

    @Test
    void ruleFourAndTheFallback() {
        CallBlockProbe probe = new CallBlockProbe(true, null);
        batch(probe, 7, PLAIN, 1, 10);
        batch(probe, 7, PLAIN, 1, 10);
        assertEquals(1, probe.count(PLAIN, Counter.P1_SINGLE_MISSES));
        assertEquals(2 + 1, probe.phase1Cost(PLAIN));
        assertEquals(2, probe.phase1RuleCost(PLAIN));
        assertEquals(2, probe.count(PLAIN, Counter.P1B_COST));
        // receivers 2, 3, 4 all dispatch to callee node 10: one direct edge
        // is cheaper than the cover {2, 3} plus a direct edge for 4
        batch(probe, 7, PLAIN, 2, 10, 3, 10);
        batch(probe, 7, PLAIN, 2, 10, 3, 10, 4, 10);
        assertEquals(1, probe.count(PLAIN, Counter.P1B_FALLBACKS));
        assertEquals(0, probe.count(PLAIN, Counter.P1B_COVERED));
        assertEquals(2 + 2 + 1, probe.count(PLAIN, Counter.P1B_COST));
    }

    @Test
    void optionValues() {
        assertNull(CallBlockProbe.of("none", null));
        assertEquals(false, CallBlockProbe.of("p1", null).simulatesPhase1b());
        assertEquals(true, CallBlockProbe.of("p1b", null).simulatesPhase1b());
        assertThrows(ConfigException.class, () -> CallBlockProbe.of("on", null));
    }
}
