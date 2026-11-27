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

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import pascal.taie.analysis.pta.CallHubsEquivalenceTest;
import pascal.taie.analysis.pta.plugin.Plugin;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The call hub table compares keys node by node: with every key hashed
 * alike (a forced collision), the solve still finds only the hub of its own
 * invoke and node set, so the results equal those without hubs. A table
 * that took an equal hash for an equal key would hand one site the targets
 * of another.
 */
public class CallHubKeyTest {

    /**
     * Hashes every key to 7 before the solve makes its first hub.
     */
    public static class CollidingHasher implements Plugin {

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onStart() {
            ((DefaultSolver) solver).setCallHubHasherForTesting((invoke, nodes, size) -> 7);
        }
    }

    @ParameterizedTest
    @CsvSource({"hubs, HubJoin, 1-call", "hubs, HubJoin, 2-obj", "blocks, Blocks, 2-call",
            "blocks, SharedCallee, 1-obj"})
    void collidingHashesKeepKeysApart(String dir, String main, String cs) {
        CallHubsEquivalenceTest.Snapshot off = CallHubsEquivalenceTest.run(dir, main, cs,
                List.of());
        CallHubsEquivalenceTest.Snapshot on = CallHubsEquivalenceTest.run(dir, main, cs,
                List.of("call-hubs:true"), List.of(CollidingHasher.class));
        CallHubsEquivalenceTest.assertSameResults(off, on, dir + " " + main + " " + cs
                + " colliding");
        assertTrue(CallHubsEquivalenceTest.counter(on.counters(), "hubs") >= 2,
                "two hubs share the hash: " + on.counters());
    }
}
