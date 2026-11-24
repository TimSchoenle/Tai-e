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
import pascal.taie.Main;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Pins the order in which the pointer analysis adds the facts of the lambda
 * programs: every new context-sensitive call edge and every new points-to
 * set of a {@code this} variable, in the order the solver reports them
 * ({@link LambdaOrderRecorder}). Both follow the work-list order, which
 * LambdaAnalysis drives with the order of its receivers, callees and
 * invocation infos. On a difference the actual listing is written to
 * {@code build/lambda-edge-order-actual.txt}.
 */
class LambdaEdgeOrderTest {

    private static final String[] MAIN_CLASSES = {
            "Args", "ImpreciseLambdas", "LambdaInstanceMethod", "LambdaSelfReceiver",
            "LambdaContexts", "DispatchBugDueToLackOfSubclassCheck",
    };

    private static final Path EXPECTED = Path.of("src/test/resources/pta/lambda/edge-order-expected.txt");

    private static final Path ACTUAL = Path.of("build/lambda-edge-order-actual.txt");

    @Test
    void factsKeepTheirOrder() throws IOException {
        List<String> actual = new ArrayList<>();
        for (String main : MAIN_CLASSES) {
            actual.add("## " + main);
            actual.addAll(listFacts(main));
        }
        List<String> expected = Files.exists(EXPECTED)
                ? Files.readAllLines(EXPECTED, StandardCharsets.UTF_8)
                : List.of();
        if (!expected.equals(actual)) {
            Files.createDirectories(ACTUAL.getParent());
            Files.write(ACTUAL, actual, StandardCharsets.UTF_8);
        }
        assertEquals(String.join("\n", expected), String.join("\n", actual));
    }

    private static List<String> listFacts(String main) {
        Main.main("-cp", "src/test/resources/pta/lambda",
                "-m", main,
                "-a", "pta=cs:1-obj;implicit-entries:false;only-app:true;"
                        + "handle-invokedynamic:true;"
                        + "plugins:[pascal.taie.analysis.pta.LambdaOrderRecorder];");
        return new ArrayList<>(LambdaOrderRecorder.EVENTS);
    }
}
