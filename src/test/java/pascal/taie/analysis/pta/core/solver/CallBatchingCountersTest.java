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

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;
import pascal.taie.analysis.Tests;
import pascal.taie.analysis.pta.plugin.Plugin;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * The counters of option {@code call-batching} (px/s116 L-B): the plain
 * offers of batched {@code processCall} and those whose callee context the
 * selector reports independent of the receiver object.
 */
public class CallBatchingCountersTest {

    private static final Pattern OFFERS =
            Pattern.compile("plain offers (\\d+) receiver_free=(\\d+)"
                    + " dispatches=(\\d+) first_offers=(\\d+)");

    /** Keeps the counters line of the last solve, read at its finish. */
    public static class CountersReader implements Plugin {

        static volatile String line;

        private DefaultSolver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = (DefaultSolver) solver;
        }

        @Override
        public void onFinish() {
            line = solver.countersLine();
        }
    }

    @AfterEach
    void dropLine() {
        CountersReader.line = null;
    }

    /**
     * @return plain offers, receiver-free offers, dispatches and first offers
     * of a solve of {@code Blocks}.
     */
    private static long[] offers(String cs, String mode) {
        return offers("Blocks", cs, mode);
    }

    private static long[] offers(String main, String cs, String mode) {
        // a solve that never finishes must not leave the previous line
        CountersReader.line = null;
        String old = System.setProperty(DefaultSolver.COUNTERS_PROPERTY, "true");
        try {
            Tests.testPTA(false, "blocks", main, "cs:" + cs,
                    "call-batching:" + mode,
                    "plugins:[" + CountersReader.class.getName() + "]");
        } finally {
            if (old == null) {
                System.clearProperty(DefaultSolver.COUNTERS_PROPERTY);
            } else {
                System.setProperty(DefaultSolver.COUNTERS_PROPERTY, old);
            }
        }
        String line = CountersReader.line;
        assertNotNull(line, "the counters line of the solve");
        Matcher m = OFFERS.matcher(line);
        if (!m.find()) {
            fail("no plain offers in: " + line);
        }
        return new long[]{Long.parseLong(m.group(1)), Long.parseLong(m.group(2)),
                Long.parseLong(m.group(3)), Long.parseLong(m.group(4))};
    }

    @Test
    void everyOfferIsReceiverFreeUnderCallSiteSelectors() {
        for (String cs : new String[]{"ci", "1-call"}) {
            long[] o = offers(cs, "batched");
            assertTrue(o[0] > 0, cs + ": offers");
            assertEquals(o[0], o[1], cs + ": receiver-free offers");
        }
    }

    @Test
    void noOfferIsReceiverFreeUnderObjectSensitivity() {
        long[] o = offers("1-obj", "batched");
        assertTrue(o[0] > 0, "offers");
        assertEquals(0, o[1], "receiver-free offers");
    }

    @Test
    void perObjectOffersAreNeverReceiverFree() {
        long[] o = offers("ci", "per-object");
        assertTrue(o[0] > 0, "offers");
        assertEquals(0, o[1], "receiver-free offers");
        assertEquals(o[0], o[3], "every per-object offer is a first offer");
    }

    /**
     * {@code SharedCallee} has call sites with several receiver objects per
     * callee: batched makes the same offers as per-object with fewer
     * dispatches, and under call-site sensitivity (one CS callee for all of
     * them) fewer first offers.
     */
    @Test
    void batchedDoesLessWorkWithSeveralReceiversPerCallee() {
        for (String cs : new String[]{"ci", "1-call", "1-obj"}) {
            long[] perObject = offers("SharedCallee", cs, "per-object");
            long[] batched = offers("SharedCallee", cs, "batched");
            assertEquals(perObject[0], batched[0], cs + ": offers");
            assertTrue(batched[2] < perObject[2], cs + ": dispatches "
                    + batched[2] + " not below " + perObject[2]);
            if (cs.equals("1-obj")) {
                assertEquals(perObject[3], batched[3], cs + ": first offers");
            } else {
                assertTrue(batched[3] < perObject[3], cs + ": first offers "
                        + batched[3] + " not below " + perObject[3]);
            }
        }
    }
}
