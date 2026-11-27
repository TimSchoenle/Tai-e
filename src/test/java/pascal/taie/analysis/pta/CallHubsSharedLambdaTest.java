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

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import pascal.taie.analysis.pta.CallHubsEquivalenceTest.Snapshot;

import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static pascal.taie.analysis.pta.CallHubsEquivalenceTest.assertSameResults;
import static pascal.taie.analysis.pta.CallHubsEquivalenceTest.counter;
import static pascal.taie.analysis.pta.CallHubsEquivalenceTest.run;

/**
 * Options {@code call-hubs} and {@code lambda-shared-edges} together keep
 * the result of the solver with neither: the CI call edges, the CS call
 * edges as distinct node edges, the reachable methods and CS methods, and
 * the points-to set of every variable and CS variable. Shared lambda edges
 * store fewer lambda edges (one per call site, callee and passing shape),
 * so the stored CS edge rows may only shrink; against lambda-shared-edges
 * alone, adding call hubs changes nothing, the stored rows included.
 */
class CallHubsSharedLambdaTest {

    private static final String INDY = "handle-invokedynamic:true";

    private static final String HUBS = "call-hubs:true";

    private static final String SHARED = "lambda-shared-edges:true";

    /**
     * @return the snapshots without both options, with shared lambda edges
     * only, and with both, after checking that all three agree
     */
    private static Snapshot[] compare(String dir, String main, String cs) {
        Snapshot off = run(dir, main, cs, List.of(INDY));
        Snapshot shared = run(dir, main, cs, List.of(INDY, SHARED));
        Snapshot both = run(dir, main, cs, List.of(INDY, SHARED, HUBS));
        String what = dir + " " + main + " " + cs;
        System.out.println("hubs + shared lambda edges " + what + ": " + both.counters()
                + " rows off=" + off.csEdges().size() + " both=" + both.csEdges().size());
        assertSameResults(shared, both, what + " hubs over shared edges");
        assertEquals(List.of(), off.violations(), what + ": views without both");
        assertEquals(off.edges(), both.edges(), what + ": CI call edges");
        assertEquals(new TreeSet<>(off.csEdges()), new TreeSet<>(both.csEdges()),
                what + ": CS call graph node edges");
        assertEquals(off.reached(), both.reached(), what + ": reachable methods");
        assertEquals(off.csReached(), both.csReached(), what + ": reachable CS methods");
        assertEquals(off.pointsTo(), both.pointsTo(), what + ": points-to sets");
        assertEquals(off.csPointsTo(), both.csPointsTo(), what + ": CS points-to sets");
        assertTrue(both.csEdges().size() <= off.csEdges().size(), what + ": stored rows");
        assertEquals(both.csEdges().size(), counter(both.counters(), "cs_edges"),
                what + ": the CS edge counter: " + both.counters());
        return new Snapshot[] {off, shared, both};
    }

    @ParameterizedTest
    @CsvSource({
            "lambda, LambdaMix, 2-obj", "lambda, LambdaMix, 1-call",
            "lambda, LambdaSharedReceiver, 1-obj", "lambda, LambdaSharedTargets, 1-obj",
            "lambda, LambdaReceiver, 2-obj", "lambda, LambdaSelfReceiver, 2-obj",
            "lambda, Streams, 1-obj", "lambda, LambdaInstanceMethod, 1-call",
            "lambda, LambdaConstructor, 1-call", "lambda, LambdaStaticMethod, 1-call",
            "lambda, LambdaContexts, 2-obj", "lambda, LambdaRedundantEdge, 1-call",
            "lambda, LambdaSharedEdges, 1-obj", "lambda, LambdaSharedEdges, 2-obj",
            "lambda, LambdaSharedEdges, ci",
            "hubs, HubJoin, 1-call", "hubs, HubCap, ci", "hubs, HubIgnored, 1-obj",
            "hubs, HubLambda, ci", "hubs, HubLambda, 1-call", "hubs, HubLambda, 1-obj"})
    void bothOptionsKeepTheResult(String dir, String main, String cs) {
        compare(dir, main, cs);
    }

    /**
     * HubLambda: the call site of make and bound links hubs, and the lambda
     * call sites have source duplicates that the shared edges drop, so both
     * options act in one solve.
     */
    @ParameterizedTest
    @CsvSource({"ci", "1-call"})
    void bothOptionsActInOneSolve(String cs) {
        Snapshot[] s = compare("hubs", "HubLambda", cs);
        String counters = s[2].counters();
        assertTrue(counter(counters, "hubs") >= 2, counters);
        assertTrue(s[2].csEdges().size() < s[0].csEdges().size(),
                "source duplicates dropped: off=" + s[0].csEdges().size()
                        + " both=" + s[2].csEdges().size());
    }
}
