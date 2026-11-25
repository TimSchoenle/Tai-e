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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import pascal.taie.Main;
import pascal.taie.analysis.pta.core.cs.selector.KCountingSelector;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.plugin.invokedynamic.LambdaAnalysis;
import pascal.taie.util.collection.Maps;

import java.lang.reflect.Field;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.HexFormat;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * LambdaAnalysis dispatches a target only on the receiver types whose
 * supertypes declare it, instead of on every receiver type: the solver
 * reports every new context-sensitive method, call edge and points-to set
 * in the same order as before (the digests below were recorded with the
 * dispatch on every receiver type), also under the verify mode, which
 * compares each grouping with the one of a dispatch on every receiver type;
 * and the analysis makes fewer dispatch calls when receiver types and
 * targets do not match.
 */
class LambdaEnterInversionTest {

    private static final String VERIFY = "spd.lambda.verify";

    private static final String OBJECT_TO_STRING = "<java.lang.Object: java.lang.String toString()>";

    /**
     * Per program: the SHA-256 of the recorded solver events and their
     * count, the same with and without a call-site free selector and the
     * verify mode.
     */
    private static final Map<String, String> ORDER = Map.of(
            "LambdaEnterMisses",
            "aafcbeb84796874090f7850cbc1941eb550b5a2ad9c17eb2cc36495f9c809e7d:37",
            "LambdaSharedReceiver",
            "96c768312f3390dd4e63211ff14e0e6c68a08504fc57944bfed0f75401607d3e:68",
            "LambdaSharedTargets",
            "184493251a8565ba0851ef94e1ac093e181b5b4b0b71d2c01be133138c2b0a53:62",
            "LambdaContexts",
            "c2f94024fc2d11ae98ff0dcc6f85543ad4684d10ce1a7e38708195927fa15d61:194",
            "Args",
            "97903eff1b8b32759cabca2b6454157a5f073725a8e6279a6a5b9272a4c4acfe:152",
            "ImpreciseLambdas",
            "64eb22daebfcd32e9239955bca95cba93f374cf4b8f6fd5bbc369baac48bb923:18",
            "LambdaInstanceMethod",
            "185678e16155b5c7d45273bb74ec8559df2902a0a78c996f068c7df86ab893d1:52",
            "LambdaSelfReceiver",
            "86d348f73d04357bf59447db514fc8387e385ce58005a62781b67e35e28ef910:21",
            "LambdaEnterSupertypes",
            "430f8283bbb41b5621d8a0d55f5ee49953821d3b3926a3b58b36147a82bd4ffe:77");

    @AfterEach
    void reset() {
        KCountingSelector.callSiteFree = false;
        System.clearProperty(VERIFY);
    }

    @ParameterizedTest
    @ValueSource(strings = {"LambdaEnterMisses", "LambdaSharedReceiver", "LambdaSharedTargets",
            "LambdaContexts", "Args", "ImpreciseLambdas", "LambdaInstanceMethod", "LambdaSelfReceiver",
            "LambdaEnterSupertypes"})
    void inversionKeepsSolverOrder(String main) throws Exception {
        List<String> expected = new ArrayList<>();
        List<String> actual = new ArrayList<>();
        Map<String, Run> runs = Maps.newOrderedMap();
        for (boolean callSiteFree : new boolean[]{false, true}) {
            for (boolean verify : new boolean[]{false, true}) {
                String key = main + "/free=" + callSiteFree + "/verify=" + verify;
                Run run = analyze(main, callSiteFree, verify);
                runs.put(key, run);
                expected.add(key + " " + ORDER.get(main));
                actual.add(key + " " + digest(run.events()) + ":" + run.events().size());
            }
        }
        // the digests first: they also compare against a build without
        // the dispatch counters
        assertEquals(String.join("\n", expected), String.join("\n", actual));
        for (Map.Entry<String, Run> entry : runs.entrySet()) {
            System.out.println("[lambda-enter] " + entry.getKey() + " enter "
                    + entry.getValue().enterCalls() + " of " + entry.getValue().enterFullScan());
        }
    }

    /**
     * Targets declared above the receiver classes: a method inherited over
     * superclasses, a default method of a superinterface of an interface,
     * and a method of {@code java.lang.Object} on an array receiver. Under
     * the verify mode every grouping restricted to the matched receiver
     * types equals the grouping over every type, and each target reaches
     * its callees.
     */
    @Test
    void inversionMatchesTargetsOfSupertypes() throws Exception {
        for (boolean callSiteFree : new boolean[]{false, true}) {
            Run run = analyze("LambdaEnterSupertypes", callSiteFree, true);
            assertTrue(run.inversionChecks() > 0, "no inversion check");
            String events = String.join("\n", run.events());
            for (String callee : new String[]{"<SupBase: java.lang.Object step()>",
                    "<SupRoot: java.lang.Object name()>",
                    "<SupImpl: java.lang.String toString()>",
                    OBJECT_TO_STRING}) {
                assertTrue(events.contains(callee), "free=" + callSiteFree + ": no " + callee);
            }
            List<String> objectThis = run.events().stream()
                    .filter(e -> e.startsWith("pts ") && e.contains(OBJECT_TO_STRING))
                    .toList();
            assertTrue(objectThis.stream().anyMatch(e -> e.contains("long[]")),
                    "free=" + callSiteFree + ": no array receiver of Object.toString in "
                            + objectThis);
        }
    }

    @Test
    void inversionSkipsDispatchMisses() throws Exception {
        for (boolean callSiteFree : new boolean[]{false, true}) {
            Run run = analyze("LambdaEnterMisses", callSiteFree, false);
            assertTrue(run.enterCalls() > 0, "no dispatch call");
            assertTrue(run.enterCalls() < run.enterFullScan(), "free=" + callSiteFree
                    + ": enter " + run.enterCalls() + " of " + run.enterFullScan());
        }
    }

    /**
     * Programs without recorded digests: the verify mode compares every
     * grouping with the one over every receiver type and throws on any
     * difference.
     */
    @ParameterizedTest
    @ValueSource(strings = {"Streams", "DispatchBugDueToLackOfSubclassCheck",
            "LambdaStaticMethod", "LambdaConstructor", "NativeModelWithLambda"})
    void verifiedInversionNeverDispatchesMore(String main) throws Exception {
        Run run = analyze(main, true, true);
        assertTrue(run.enterCalls() <= run.enterFullScan(),
                "enter " + run.enterCalls() + " of " + run.enterFullScan());
    }

    private record Run(List<String> events, LambdaAnalysis lambda, Object verifier) {

        long enterCalls() throws ReflectiveOperationException {
            return (long) field(lambda, "enterCalls");
        }

        long enterFullScan() throws ReflectiveOperationException {
            return (long) field(lambda, "enterFullScan");
        }

        long inversionChecks() throws ReflectiveOperationException {
            return (long) field(Objects.requireNonNull(verifier, "verify mode off"),
                    "inversionChecks");
        }
    }

    private static Run analyze(String main, boolean callSiteFree, boolean verify)
            throws ReflectiveOperationException {
        KCountingSelector.callSiteFree = callSiteFree;
        if (verify) {
            System.setProperty(VERIFY, "true");
        } else {
            System.clearProperty(VERIFY);
        }
        Main.main("-cp", "src/test/resources/pta/lambda",
                "-m", main,
                "-a", "pta=cs:1-counting;implicit-entries:false;only-app:true;"
                        + "handle-invokedynamic:true;"
                        + "plugins:[pascal.taie.analysis.pta.SolverOrderRecorder,"
                        + Probe.class.getName() + "];");
        return new Run(new ArrayList<>(SolverOrderRecorder.EVENTS), lambdaAnalysis(),
                Probe.verifier);
    }

    private static String digest(List<String> events) throws NoSuchAlgorithmException {
        MessageDigest sha = MessageDigest.getInstance("SHA-256");
        for (String event : events) {
            sha.update(event.getBytes(StandardCharsets.UTF_8));
            sha.update((byte) '\n');
        }
        return HexFormat.of().formatHex(sha.digest());
    }

    private static LambdaAnalysis lambdaAnalysis() throws ReflectiveOperationException {
        Object composite = field(Probe.solver, "plugin");
        for (Object plugin : (List<?>) field(composite, "allPlugins")) {
            if (plugin instanceof LambdaAnalysis lambda) {
                return lambda;
            }
        }
        throw new AssertionError("no LambdaAnalysis");
    }

    private static Object field(Object owner, String name) throws ReflectiveOperationException {
        Class<?> c = owner.getClass();
        while (c != null) {
            try {
                Field f = c.getDeclaredField(name);
                f.setAccessible(true);
                return f.get(owner);
            } catch (NoSuchFieldException e) {
                c = c.getSuperclass();
            }
        }
        throw new NoSuchFieldException(name);
    }

    /**
     * Keeps the solver of the last run and the verifier of its lambda
     * analysis, which the analysis drops at the finish check.
     */
    public static class Probe implements Plugin {

        static Solver solver;

        static Object verifier;

        @Override
        public void setSolver(Solver solver) {
            Probe.solver = solver;
        }

        @Override
        public void onStart() {
            try {
                verifier = field(lambdaAnalysis(), "verifier");
            } catch (ReflectiveOperationException e) {
                throw new IllegalStateException("no verifier field", e);
            }
        }
    }
}
