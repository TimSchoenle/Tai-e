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
import pascal.taie.Main;
import pascal.taie.analysis.pta.plugin.Plugin;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks that the solver hands a large delta that a pointer takes whole on
 * as the difference, so that the work list passes it to the successors by
 * reference, with and without shared points-to sets.
 */
class WorkListWaveTest {

    @Test
    void unchangedLargeDeltasTravelByReference() {
        assertTrue(referencedEntries("pack-pending-deltas:false;") > 0, Probe.line);
    }

    @Test
    void unchangedLargeDeltasTravelByReferenceWithSharedSets() {
        assertTrue(referencedEntries("pack-pending-deltas:false;share-points-to-sets:true;") > 0,
                Probe.line);
    }

    @Test
    void packedDeltasAreNotReferenced() {
        assertEquals(0, referencedEntries(""), Probe.line);
    }

    private static long referencedEntries(String options) {
        Probe.line = null;
        Main.main("-cp", "src/test/resources/pta/census",
                "-m", "Census",
                "-a", "pta=" + options + "plugins:[" + Probe.class.getName() + "];");
        String line = Probe.line;
        assertNotNull(line, "no work list counters at onFinish");
        String key = " referenced_entries=";
        int at = line.indexOf(key);
        assertTrue(at >= 0, line);
        int start = at + key.length();
        int end = line.indexOf(' ', start);
        return Long.parseLong(line.substring(start, end < 0 ? line.length() : end));
    }

    /**
     * Reads the work list counters at onFinish. Public with a no-argument
     * constructor: the analysis loads it by name.
     */
    public static class Probe implements Plugin {

        static String line;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            line = ((DefaultSolver) solver).workListCountersLine();
        }
    }
}
