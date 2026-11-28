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

package pascal.taie.analysis.pta;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import java.util.ArrayList;
import java.util.List;

/**
 * Option {@code pack-pending-deltas}: packed pending work list deltas (a
 * merge that adds nothing answered on the packed words, any other merge
 * restoring them) give the same results as unpacked deltas: the CI and CS
 * call edges, the reachable methods and CS methods, and the points-to set
 * of every variable and every CS variable (see
 * {@link CallHubsEquivalenceTest#assertSameResults}).
 */
public class PendingDeltaPackingEquivalenceTest {

    @AfterEach
    void clear() {
        CallHubsEquivalenceTest.HubWatcher.VIOLATIONS.clear();
        CallHubsEquivalenceTest.HubWatcher.counters = "";
    }

    /**
     * @param more further options separated by {@code ;}, or empty
     */
    @ParameterizedTest
    @CsvSource(delimiter = '|', value = {
            "blocks | Blocks | ci |", "blocks | Blocks | 1-call |", "blocks | Blocks | 2-obj |",
            "blocks | Blocks | 2-obj | share-points-to-sets:true",
            "blocks | Blocks | 1-call | share-points-to-sets:true",
            "blocks | SharedCallee | 1-obj | share-points-to-sets:true",
            "hubs | HubJoin | 1-call |", "lambda | LambdaMix | 2-obj | share-points-to-sets:true",
            "lambda | Streams | 1-obj |", "basic | Dispatch | 2-obj |",
            "misc | Zipper | 2-obj | advanced:zipper"})
    void packingChangesNoResult(String dir, String main, String cs, String more) {
        List<String> extra = more == null ? List.of() : List.of(more.split(";"));
        List<String> unpacked = new ArrayList<>(extra);
        unpacked.add("pack-pending-deltas:false");
        List<String> packed = new ArrayList<>(extra);
        packed.add("pack-pending-deltas:true");
        CallHubsEquivalenceTest.Snapshot off = CallHubsEquivalenceTest.run(dir, main, cs, unpacked);
        CallHubsEquivalenceTest.Snapshot on = CallHubsEquivalenceTest.run(dir, main, cs, packed);
        CallHubsEquivalenceTest.assertSameResults(off, on, dir + " " + main + " " + cs + " " + extra);
    }
}
