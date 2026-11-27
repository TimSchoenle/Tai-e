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
import pascal.taie.analysis.pta.core.solver.CallBlockProbe.Mode;
import pascal.taie.config.ConfigException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The counters of {@link CallBlockProbe} on batches with known sharing. A
 * batch is offered as pairs (object index, callee key) at a site; a callee
 * node is fresh unless the test says otherwise.
 */
class CallBlockProbeTest {

    private static final EdgeClass PLAIN = EdgeClass.PLAIN;

    private static CallBlockProbe.Batch begin(CallBlockProbe probe, long site,
                                              EdgeClass edgeClass) {
        return probe.begin(site, site, edgeClass);
    }

    /** Offers {@code pairs} (object, callee, object, callee, ...) as one batch, all fresh. */
    private static void batch(CallBlockProbe probe, long site, EdgeClass edgeClass,
                              int... pairs) {
        CallBlockProbe.Batch batch = begin(probe, site, edgeClass);
        for (int i = 0; i < pairs.length; i += 2) {
            batch.offer(pairs[i], pairs[i + 1], pairs[i + 1]);
        }
        probe.end(batch);
    }

    /**
     * Offers {@code triples} (object, callee, fresh 1 or 0, ...) as one
     * plain batch at site 7.
     */
    private static void freshBatch(CallBlockProbe probe, int... triples) {
        CallBlockProbe.Batch batch = begin(probe, 7, PLAIN);
        for (int i = 0; i < triples.length; i += 3) {
            batch.offer(triples[i], triples[i + 1], triples[i + 2] == 1 ? triples[i + 1] : null);
        }
        probe.end(batch);
    }

    @Test
    void twoContextsWithTheSameReceiverSetShareOneBlock() {
        CallBlockProbe probe = new CallBlockProbe(Mode.P1B, null);
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
        assertEquals(2, probe.phase1StoredPairs(PLAIN));
        // two hub references plus two target edges
        assertEquals(4, probe.phase1Cost(PLAIN));
        assertEquals(4, probe.phase1RuleCost(PLAIN));
        assertEquals(1, probe.count(PLAIN, Counter.P1B_HITS));
        assertEquals(1 + 2 + 1, probe.count(PLAIN, Counter.P1B_COST));
        assertEquals(2, probe.count(PLAIN, Counter.P1B_BLOCK_PAIRS));
        // the empty batch counts nothing
        batch(probe, 7, PLAIN);
        assertEquals(2, probe.count(PLAIN, Counter.BATCHES));
    }

    @Test
    void blocksAreKeptPerSiteAndClass() {
        CallBlockProbe probe = new CallBlockProbe(Mode.P1, null);
        batch(probe, 7, PLAIN, 1, 10, 2, 20);
        batch(probe, 8, PLAIN, 1, 10, 2, 20);
        batch(probe, 7, EdgeClass.LAMBDA_BOUND, 1, 10, 2, 20);
        assertEquals(0, probe.count(PLAIN, Counter.P1_HITS));
        assertEquals(2, probe.count(PLAIN, Counter.P1_BLOCKS));
        assertEquals(1, probe.count(EdgeClass.LAMBDA_BOUND, Counter.P1_BLOCKS));
        // a pair with another callee node is another content
        batch(probe, 7, PLAIN, 1, 10, 2, 21);
        assertEquals(3, probe.count(PLAIN, Counter.P1_BLOCKS));
        // target hubs are kept per site and class too
        assertEquals(0, probe.count(PLAIN, Counter.P1T_HITS));
        assertEquals(3, probe.count(PLAIN, Counter.P1T_HUBS));
        assertEquals(1, probe.count(EdgeClass.LAMBDA_BOUND, Counter.P1T_HUBS));
    }

    @Test
    void aLateJoinerIsCoveredInPhase1b() {
        CallBlockProbe probe = new CallBlockProbe(Mode.P1B, null);
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
        CallBlockProbe probe = new CallBlockProbe(Mode.P1B, null);
        batch(probe, 7, PLAIN, 1, 10);
        batch(probe, 7, PLAIN, 1, 10);
        assertEquals(1, probe.count(PLAIN, Counter.P1_SINGLE_MISSES));
        assertEquals(2, probe.count(PLAIN, Counter.P1_SINGLES));
        assertEquals(2 + 1, probe.phase1Cost(PLAIN));
        assertEquals(2, probe.phase1RuleCost(PLAIN));
        assertEquals(2, probe.count(PLAIN, Counter.P1B_COST));
        assertEquals(0, probe.phase1StoredPairs(PLAIN));
        // receivers 2, 3, 4 all dispatch to callee node 10: one direct edge
        // is cheaper than the cover {2, 3} plus a direct edge for 4
        batch(probe, 7, PLAIN, 2, 10, 3, 10);
        batch(probe, 7, PLAIN, 2, 10, 3, 10, 4, 10);
        assertEquals(1, probe.count(PLAIN, Counter.P1B_FALLBACKS));
        assertEquals(0, probe.count(PLAIN, Counter.P1B_COVERED));
        assertEquals(2 + 2 + 1, probe.count(PLAIN, Counter.P1B_COST));
    }

    @Test
    void freshCountsDistinctUnlinkedCalleeNodes() {
        CallBlockProbe probe = new CallBlockProbe(Mode.P1, null);
        CallBlockProbe.Batch batch = begin(probe, 7, PLAIN);
        // callee 10 is fresh (offered twice), callee 20 is linked already
        batch.offer(1, 10, 10);
        batch.offer(2, 10, 10);
        batch.offer(3, 20, null, 2, 1);
        probe.end(batch);
        assertEquals(2, probe.count(PLAIN, Counter.DIRECT));
        assertEquals(1, probe.count(PLAIN, Counter.FRESH));
        assertEquals(0, probe.count(PLAIN, Counter.STALE));
        assertEquals(1, probe.count(PLAIN, Counter.P1T_SINGLES));
        // a linked node has no weight
        assertEquals(0, probe.count(PLAIN, Counter.W_TODAY));
        // a batch whose callee nodes are all linked is stale
        freshBatch(probe, 4, 10, 0, 5, 20, 0);
        assertEquals(1, probe.count(PLAIN, Counter.FRESH));
        assertEquals(1, probe.count(PLAIN, Counter.STALE));
        assertEquals(2, probe.count(PLAIN, Counter.BATCHES));
    }

    @Test
    void aBatchOfOnePairCostsItsFreshEdge() {
        CallBlockProbe probe = new CallBlockProbe(Mode.P1B, null);
        // a miss whose edge exists costs nothing, a fresh one one edge
        freshBatch(probe, 1, 10, 0);
        assertEquals(0, probe.phase1RuleCost(PLAIN));
        assertEquals(0, probe.count(PLAIN, Counter.P1B_COST));
        assertEquals(0, probe.count(PLAIN, Counter.P1T_COST));
        freshBatch(probe, 2, 20, 1);
        assertEquals(1, probe.phase1RuleCost(PLAIN));
        assertEquals(1, probe.count(PLAIN, Counter.P1B_COST));
        assertEquals(1, probe.count(PLAIN, Counter.P1T_COST));
        // a hit of one pair: 0 when linked, 1 when fresh
        freshBatch(probe, 2, 20, 0);
        assertEquals(1, probe.phase1RuleCost(PLAIN));
        freshBatch(probe, 2, 20, 1);
        assertEquals(2, probe.phase1RuleCost(PLAIN));
        assertEquals(2, probe.count(PLAIN, Counter.P1B_COST));
        assertEquals(2, probe.count(PLAIN, Counter.P1T_COST));
        assertEquals(2, probe.count(PLAIN, Counter.P1_HITS));
    }

    @Test
    void equalFreshSetsOfTwoContextsShareOneTargetHub() {
        CallBlockProbe probe = new CallBlockProbe(Mode.P1T, null);
        // contexts A and B of one invoke: other receivers, the same callee nodes
        freshBatch(probe, 1, 10, 1, 2, 20, 1);
        freshBatch(probe, 3, 20, 1, 4, 10, 1, 5, 10, 1);
        assertEquals(1, probe.count(PLAIN, Counter.P1T_HUBS));
        assertEquals(1, probe.count(PLAIN, Counter.P1T_HITS));
        assertEquals(2, probe.count(PLAIN, Counter.P1T_REFS));
        assertEquals(2, probe.count(PLAIN, Counter.P1T_TARGETS));
        assertEquals(1 + 2 + 1, probe.count(PLAIN, Counter.P1T_COST));
        // p1t keeps no phase-1 blocks
        assertEquals(0, probe.count(PLAIN, Counter.P1_BLOCKS));
        assertFalse(probe.simulatesPhase1());
    }

    @Test
    void aGrowingSetKeysOnlyItsNewNodes() {
        CallBlockProbe probe = new CallBlockProbe(Mode.P1T, null);
        // node 10 gets two argument edges and one return edge, node 20 one return edge
        CallBlockProbe.Batch first = begin(probe, 7, PLAIN);
        first.offer(1, 10, 10, 2, 1);
        first.offer(2, 20, 20, 0, 1);
        probe.end(first);
        // the same context later: 10 and 20 are linked, 30 and 40 are new
        freshBatch(probe, 1, 10, 0, 2, 20, 0, 3, 30, 1, 4, 40, 1);
        assertEquals(2, probe.count(PLAIN, Counter.P1T_HUBS));
        assertEquals(4, probe.count(PLAIN, Counter.P1T_TARGETS));
        assertEquals(0, probe.count(PLAIN, Counter.P1T_HITS));
        // another context with the set {30, 40} joins the second hub
        freshBatch(probe, 5, 30, 1, 6, 40, 1);
        assertEquals(1, probe.count(PLAIN, Counter.P1T_HITS));
        // one new node is a direct edge, no hub
        freshBatch(probe, 7, 50, 1, 8, 10, 0);
        assertEquals(2, probe.count(PLAIN, Counter.P1T_HUBS));
        assertEquals(3 + 3 + 1 + 1, probe.count(PLAIN, Counter.P1T_COST));
        // the weights come from the first batch only: 4 PFG edges today, all
        // on targets of a new key; its hub has 2 argument positions and a result
        assertEquals(4, probe.count(PLAIN, Counter.W_TODAY));
        assertEquals(4, probe.count(PLAIN, Counter.W_TARGETS));
        assertEquals(0, probe.count(PLAIN, Counter.W_DIRECT));
        assertEquals(3, probe.count(PLAIN, Counter.W_JOIN));
        assertEquals(3, probe.count(PLAIN, Counter.W_JOIN1));
        // only the key {30, 40} got a second member, and its first had no positions
        assertEquals(1, probe.count(PLAIN, Counter.P1T_HUB1));
        assertEquals(1, probe.count(PLAIN, Counter.P1T_HUB2));
        assertEquals(0, probe.count(PLAIN, Counter.HUB_PTRS2));
    }

    @Test
    void hubPointersOfSharedKeysAndDirectWeights() {
        CallBlockProbe probe = new CallBlockProbe(Mode.P1T, null);
        for (int member = 0; member < 3; ++member) {
            CallBlockProbe.Batch batch = begin(probe, 7, PLAIN);
            batch.offer(member, 10, 10, 1, 0);
            batch.offer(member, 20, 20, 1, 2);
            probe.end(batch);
        }
        // three members of one key: weights of the first count as targets
        assertEquals(3 * 4, probe.count(PLAIN, Counter.W_TODAY));
        assertEquals(4, probe.count(PLAIN, Counter.W_TARGETS));
        assertEquals(3 * 2, probe.count(PLAIN, Counter.W_JOIN));
        assertEquals(2, probe.count(PLAIN, Counter.W_JOIN1));
        assertEquals(2, probe.count(PLAIN, Counter.HUB_PTRS2));
        assertEquals(0, probe.count(PLAIN, Counter.P1T_HUB1));
        assertEquals(1, probe.count(PLAIN, Counter.P1T_HUB2));
        // a single fresh node is a direct edge with its weight
        CallBlockProbe.Batch single = begin(probe, 7, PLAIN);
        single.offer(5, 30, 30, 3, 1);
        probe.end(single);
        assertEquals(4, probe.count(PLAIN, Counter.W_DIRECT));
        // a new key (1 + 2), two hits and the direct edge
        assertEquals(3 + 1 + 1 + 1, probe.count(PLAIN, Counter.P1T_COST));
    }

    @Test
    void unequalSetsWithEqualHashesAreTwoKeys() {
        // every node set hashes alike, so only equality tells keys apart
        CallBlockProbe probe = new CallBlockProbe(Mode.P1T, null, nodes -> 0);
        freshBatch(probe, 1, 10, 1, 2, 20, 1);
        freshBatch(probe, 1, 30, 1, 2, 40, 1);
        assertEquals(2, probe.count(PLAIN, Counter.P1T_HUBS));
        freshBatch(probe, 3, 20, 1, 4, 10, 1);
        assertEquals(1, probe.count(PLAIN, Counter.P1T_HITS));
        // nodes with equal hash codes are still told apart
        CallBlockProbe exact = new CallBlockProbe(Mode.P1T, null);
        assertEquals("Aa".hashCode(), "BB".hashCode());
        for (String node : new String[] {"Aa", "BB", "Aa"}) {
            CallBlockProbe.Batch batch = begin(exact, 7, PLAIN);
            batch.offer(1, node.hashCode(), node);
            batch.offer(1, 99, "x");
            exact.end(batch);
        }
        assertEquals(2, exact.count(PLAIN, Counter.P1T_HUBS));
        assertEquals(1, exact.count(PLAIN, Counter.P1T_HITS));
        // and one batch offering both counts both as fresh
        CallBlockProbe.Batch both = begin(exact, 8, PLAIN);
        both.offer(1, "Aa".hashCode(), "Aa");
        both.offer(2, "BB".hashCode(), "BB");
        both.offer(3, "BB".hashCode(), "BB");
        exact.end(both);
        assertEquals(6 + 2, exact.count(PLAIN, Counter.FRESH));
    }

    @Test
    void optionValues() {
        assertNull(CallBlockProbe.of("none", null));
        assertFalse(CallBlockProbe.of("p1", null).simulatesPhase1b());
        assertTrue(CallBlockProbe.of("p1b", null).simulatesPhase1b());
        assertFalse(CallBlockProbe.of("p1t", null).simulatesPhase1());
        assertTrue(CallBlockProbe.of("p1t", null).line().startsWith("p1t; plain"));
        assertThrows(ConfigException.class, () -> CallBlockProbe.of("on", null));
    }
}
