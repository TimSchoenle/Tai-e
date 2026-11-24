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
import org.junit.jupiter.params.provider.ValueSource;
import pascal.taie.Main;
import pascal.taie.analysis.pta.core.cs.selector.KCountingSelector;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * With a selector whose instance contexts are call-site free, the lambda
 * invocations of one target on a receiver variable share one grouping per
 * new points-to set: the analysis then selects fewer instance contexts, and
 * reports every new context-sensitive method, call edge and points-to set
 * in the same order as with one grouping per invocation.
 */
class LambdaSharedGroupingTest {

    @AfterEach
    void resetSelector() {
        KCountingSelector.callSiteFree = false;
    }

    @ParameterizedTest
    @ValueSource(strings = {"LambdaSharedReceiver", "LambdaSharedTargets",
            "LambdaContexts", "Args", "ImpreciseLambdas", "LambdaInstanceMethod", "LambdaSelfReceiver"})
    void sharedGroupingKeepsFactsAndOrder(String main) {
        Run perInvocation = analyze(main, false);
        Run shared = analyze(main, true);
        System.out.println("[lambda-shared] " + main + " instance selections: per invocation "
                + perInvocation.selections() + ", shared " + shared.selections());
        assertEquals(String.join("\n", perInvocation.events()),
                String.join("\n", shared.events()));
        assertTrue(shared.selections() <= perInvocation.selections(),
                "shared " + shared.selections() + " > per invocation "
                        + perInvocation.selections());
    }

    @ParameterizedTest
    @ValueSource(strings = {"LambdaSharedReceiver", "LambdaSharedTargets"})
    void sharedGroupingSelectsFewerContexts(String main) {
        Run perInvocation = analyze(main, false);
        Run shared = analyze(main, true);
        assertTrue(shared.selections() < perInvocation.selections(),
                "shared " + shared.selections() + ", per invocation "
                        + perInvocation.selections());
    }

    private record Run(List<String> events, long selections) {
    }

    private static Run analyze(String main, boolean callSiteFree) {
        KCountingSelector.callSiteFree = callSiteFree;
        KCountingSelector.INSTANCE_SELECTIONS.set(0);
        Main.main("-cp", "src/test/resources/pta/lambda",
                "-m", main,
                "-a", "pta=cs:1-counting;implicit-entries:false;only-app:true;"
                        + "handle-invokedynamic:true;"
                        + "plugins:[pascal.taie.analysis.pta.SolverOrderRecorder];");
        return new Run(new ArrayList<>(SolverOrderRecorder.EVENTS),
                KCountingSelector.INSTANCE_SELECTIONS.get());
    }
}
