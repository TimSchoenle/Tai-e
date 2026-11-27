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

package pascal.taie.analysis.pta.plugin.invokedynamic;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.lang.reflect.Field;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * The verify mode of {@link LambdaAnalysis} checks the calls of lambda
 * objects that are receivers of a method reference (fixture
 * {@code LambdaReceiver}): it counts them on the fixture, and fails a run
 * in which such a call is queued but never drained, or drained but never
 * made. The faults are injected by {@link Probe} through reflection.
 */
class LambdaReceiverVerifyTest {

    private static final String VERIFY = "spd.lambda.verify";

    private static final String OPTIONS = "cs:ci;implicit-entries:false;only-app:true;"
            + "handle-invokedynamic:true;plugins:[" + Probe.class.getName() + "];";

    private static final Pattern RECEIVER_CHECKS = Pattern.compile("receiverCallChecks=(\\d+)");

    @BeforeEach
    void verifyOn() {
        System.setProperty(VERIFY, "true");
    }

    @AfterEach
    void verifyOff() {
        System.clearProperty(VERIFY);
        Probe.fault = Fault.NONE;
    }

    @Test
    void verifyModeChecksTheLambdaReceiverCalls() {
        Probe.fault = Fault.NONE;
        PrintStream out = System.out;
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        System.setOut(new PrintStream(captured, true, StandardCharsets.UTF_8));
        try {
            run();
        } finally {
            System.setOut(out);
        }
        List<String> finishLines = captured.toString(StandardCharsets.UTF_8).lines()
                .filter(line -> line.contains("[spd] lambda verify finish OK"))
                .toList();
        assertTrue(finishLines.size() == 1, finishLines.toString());
        Matcher m = RECEIVER_CHECKS.matcher(finishLines.get(0));
        assertTrue(m.find(), finishLines.get(0));
        assertTrue(Long.parseLong(m.group(1)) > 0, finishLines.get(0));
    }

    @Test
    void verifyModeFailsACallLeftQueued() {
        Probe.fault = Fault.STUCK_DRAIN;
        assertFailsWith("lambda receiver calls left queued");
    }

    @Test
    void verifyModeFailsACallLostAfterQueueing() {
        Probe.fault = Fault.LOST_CALLS;
        assertFailsWith("missing");
    }

    private static void assertFailsWith(String text) {
        Throwable thrown = assertThrows(Throwable.class, LambdaReceiverVerifyTest::run);
        for (Throwable t = thrown; t != null; t = t.getCause()) {
            String message = t.getMessage();
            if (message != null && message.contains("lambda verify")
                    && message.contains(text)) {
                return;
            }
        }
        fail("no lambda verify failure with \"" + text + "\"", thrown);
    }

    private static void run() {
        Main.main("-cp", "src/test/resources/pta/lambda", "-m", "LambdaReceiver",
                "-a", "pta=" + OPTIONS);
    }

    private enum Fault {
        NONE,
        /**
         * The drain never runs, so queued calls stay queued.
         */
        STUCK_DRAIN,
        /**
         * Every queued call is dropped at its dedupe, so no call is made.
         */
        LOST_CALLS
    }

    /**
     * Injects {@link #fault} into the run's {@link LambdaAnalysis} at the
     * start of the solve.
     */
    public static class Probe implements Plugin {

        static Fault fault = Fault.NONE;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onStart() {
            try {
                LambdaAnalysis lambda = lambdaAnalysis();
                switch (fault) {
                    case NONE -> {
                    }
                    case STUCK_DRAIN -> field("drainingLambdaReceiverCalls").setBoolean(lambda, true);
                    case LOST_CALLS -> field("chainedCalls").set(lambda, new ChainedCalls() {
                        @Override
                        boolean add(CSCallSite csCallSite, LambdaSource source) {
                            return false;
                        }
                    });
                }
            } catch (ReflectiveOperationException | IllegalArgumentException e) {
                throw new AssertionError("cannot inject " + fault, e);
            }
        }

        private LambdaAnalysis lambdaAnalysis() throws ReflectiveOperationException {
            Field pluginField = solver.getClass().getDeclaredField("plugin");
            pluginField.setAccessible(true);
            Object composite = pluginField.get(solver);
            Field allField = composite.getClass().getDeclaredField("allPlugins");
            allField.setAccessible(true);
            for (Object plugin : (List<?>) allField.get(composite)) {
                if (plugin instanceof LambdaAnalysis lambda) {
                    return lambda;
                }
            }
            throw new AssertionError("no LambdaAnalysis");
        }

        private static Field field(String name) throws NoSuchFieldException {
            Field f = LambdaAnalysis.class.getDeclaredField(name);
            f.setAccessible(true);
            return f;
        }
    }
}
