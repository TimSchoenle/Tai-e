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

import static pascal.taie.analysis.pta.CallHubsEquivalenceTest.assertSameResults;
import static pascal.taie.analysis.pta.CallHubsEquivalenceTest.run;

/**
 * The option {@code lambda-shared-receiver-groups} keeps the fixpoint: with
 * shared points-to sets, the CI and CS call edges, the reachable methods
 * and CS methods and the points-to set of every variable and CS variable
 * equal those of one grouping per variable, with the lambda grouping
 * verifier on (it checks every grouping against the variable's points-to
 * set). The fixtures include receiver variables that share one set
 * (LambdaSharedReceiver, LambdaSharedTargets) and invocations whose receiver
 * is the variable being propagated (LambdaSelfReceiver).
 */
class LambdaSharedReceiverGroupsTest {

    private static final String VERIFY = "spd.lambda.verify";

    @AfterEach
    void clearVerify() {
        System.clearProperty(VERIFY);
    }

    private static CallHubsEquivalenceTest.Snapshot solve(
            String dir, String main, String cs, String more, boolean shared) {
        List<String> opts = new ArrayList<>(List.of("handle-invokedynamic:true",
                "share-points-to-sets:true", "lambda-shared-receiver-groups:" + shared));
        if (!more.isEmpty()) {
            opts.addAll(List.of(more.split(";")));
        }
        return run(dir, main, cs, opts);
    }

    @ParameterizedTest
    @CsvSource(delimiter = '|', value = {
            "lambda | LambdaMix | 2-obj | ", "lambda | LambdaMix | 1-call | ",
            "lambda | LambdaSharedReceiver | 1-obj | ",
            "lambda | LambdaSharedReceiver | ci | ",
            "lambda | LambdaSharedTargets | 1-obj | ", "lambda | LambdaReceiver | 2-obj | ",
            "lambda | LambdaSelfReceiver | 2-obj | ", "lambda | LambdaSelfReceiver | ci | ",
            "lambda | Streams | 1-obj | ", "lambda | Streams | ci | ",
            "lambda | LambdaInstanceMethod | 1-call | ",
            "lambda | LambdaConstructor | 1-call | ", "lambda | LambdaContexts | 2-obj | ",
            "lambda | LambdaRedundantEdge | 1-call | ",
            "lambda | LambdaSharedEdges | 1-obj | lambda-shared-edges:true",
            "lambda | LambdaSharedEdges | ci | lambda-shared-edges:true",
            "lambda | LambdaMix | 2-obj | pack-cold-sets:4",
            "hubs | HubJoin | 1-call | call-hubs:true", "hubs | HubCap | ci | call-hubs:true",
            "hubs | HubIgnored | 1-obj | call-hubs:true",
            "hubs | HubLambda | ci | call-hubs:true;lambda-shared-edges:true",
            "hubs | HubLambda | 1-call | call-hubs:true",
            "hubs | HubLambda | 1-obj | call-hubs:true"})
    void sharedGroupingsKeepTheResult(String dir, String main, String cs, String more) {
        String extra = more == null ? "" : more;
        CallHubsEquivalenceTest.Snapshot off = solve(dir, main, cs, extra, false);
        System.setProperty(VERIFY, "true");
        CallHubsEquivalenceTest.Snapshot on = solve(dir, main, cs, extra, true);
        assertSameResults(off, on, dir + " " + main + " " + cs + " " + extra);
    }
}
