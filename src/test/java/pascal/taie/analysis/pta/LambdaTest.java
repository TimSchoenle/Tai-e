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

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import pascal.taie.analysis.Tests;

public class LambdaTest {

    private static final String DIR = "lambda";

    private static final String ARG = "handle-invokedynamic:true";

    @ParameterizedTest
    @ValueSource(strings = {
            "Args",
            "LambdaConstructor",
            "LambdaInstanceMethod",
            "LambdaStaticMethod",
            "ImpreciseLambdas",
            "DispatchBugDueToLackOfSubclassCheck",
            "NativeModelWithLambda",
    })
    void test(String mainClass) {
        Tests.testPTA(DIR, mainClass, ARG);
    }

    /**
     * Runs LambdaAnalysis's verify mode on invocations whose receiver
     * variable is the base variable being propagated: the verify mode
     * replays the per-object path beside the grouped one and checks every
     * replayed fact in the final solver state, throwing on any difference.
     */
    @Test
    void testVerifiedSelfReceiver() {
        String key = "spd.lambda.verify";
        System.setProperty(key, "true");
        try {
            Tests.testPTA(false, DIR, "LambdaSelfReceiver", ARG);
        } finally {
            System.clearProperty(key);
        }
    }

}
