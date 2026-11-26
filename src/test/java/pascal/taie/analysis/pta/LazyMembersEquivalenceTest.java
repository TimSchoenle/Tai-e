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

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.Tests;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.reflection.LazyMembers;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassMember;
import pascal.taie.language.classes.JMethod;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Lazy reflection members (option {@code reflection-members-lazy},
 * px/s115-P52) against concrete member objects: on every reflection
 * fixture, a run with the option off and a run with threshold N give equal
 * call edges, equal reachable methods and, with each placeholder replaced by
 * its members, equal points-to sets of every variable; the fixtures'
 * PTAAssert checks hold in both runs.
 */
public class LazyMembersEquivalenceTest {

    private static final String MEMBERS = "reflection-members:true";

    private static final String OFF = "reflection-members-lazy:-1";

    private static final String LAZY = "reflection-members-lazy:";

    /** Marker option of {@link #run}: run without the PTAAssert checks. */
    private static final String NO_ASSERTIONS = "no-assertions";

    private static final String PTA_ROOT = "src/test/resources/pta";

    /** Descriptor text of the concrete member objects of reflection inference. */
    private static final String MEMBER_DESC = "ReflectionMetaObj";

    /** Descriptor text of the objects that hold the unified member fields. */
    private static final String MEMBER_FIELDS_DESC = "ReflectionMemberFields";

    private static final String UNIFY = "reflection-members-unify:true";

    private static final String VERIFY = "px.lazymembers.verify";

    /** Every lazy run of this class ends with the in-run check. */
    @BeforeAll
    static void enableTheInRunCheck() {
        System.setProperty(VERIFY, "true");
    }

    @AfterAll
    static void disableTheInRunCheck() {
        System.clearProperty(VERIFY);
    }

    @ParameterizedTest
    @CsvSource({
            "reflsound, TypeMatch, 0", "reflsound, ArgTypes, 0",
            "reflsound, GetMethodIface, 0", "reflsound, MemberArrays, 0",
            "reflsound, ClassInit, 0", "reflsound, LazyGrowth, 0",
            "reflsound, LazyGrowth, 1", "reflsound, MemberArrays, 1",
            "reflsound, LazyNamed, 0", "reflsound, LazyNamed, 1",
    })
    void reflectionSoundnessFixtures(String dir, String main, int threshold) {
        Comparison comparison = compare(dir, main, threshold);
        // at N=1 a call site with one receiver class keeps it eager
        if (threshold == 0 || main.startsWith("Lazy")) {
            assertTrue(comparison.lazy().placeholders() > 0,
                    main + " holds no placeholder at N=" + threshold);
        }
    }

    /**
     * Context-sensitive runs at N=1: the eager classes and the placeholder
     * are per call context.
     */
    @ParameterizedTest
    @CsvSource({"LazyNamed", "LazyGrowth"})
    void contextSensitiveAtThresholdOne(String main) {
        Comparison comparison = compare("reflsound", main, 1, "cs:1-call");
        assertTrue(comparison.lazy().placeholders() > 0);
    }

    /**
     * Two runs give the same raw output: every points-to set in its own
     * order (the order in which the objects were made), placeholder texts
     * included, so neither the objects' order nor the split of each call
     * site's classes into eager and lazy depends on identity hashes. The
     * lines are sorted, as the order of the call graph's edges and of the
     * pointers is a hash order of the solver's maps with the option off too.
     */
    @Test
    void lazyRunsAreDeterministic() {
        List<String> first = rawOutput("LazyNamed");
        List<String> second = rawOutput("LazyNamed");
        assertTrue(first.stream().anyMatch(line -> line.contains("LazyMembers{")),
                "no placeholder in the raw output");
        assertEquals(first, second);
    }

    /**
     * The in-run check runs at the end of every lazy run of this class; here
     * it is seen to check placeholders, subscriptions and consumer sites.
     */
    @Test
    void verifierChecksThePlaceholdersAndTheirConsumers() {
        PrintStream original = System.err;
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        System.setErr(new PrintStream(captured, true, StandardCharsets.UTF_8));
        try {
            run("reflsound", "LazyGrowth", LAZY + 0);
        } finally {
            System.setErr(original);
        }
        String report = captured.toString(StandardCharsets.UTF_8).lines()
                .filter(line -> line.startsWith("[refl] lazy members verified"))
                .findFirst().orElseThrow(() -> new AssertionError("the check did not run"));
        assertTrue(!report.contains("placeholders=0") && !report.contains("subscriptions=0")
                && !report.contains("consumer_receivers=0"), report);
    }

    /**
     * Option reflection-members-unify turns the member-field unification on
     * with lazy members off: the instance fields of member objects then hang
     * on the shared objects, and on these fixtures the call graph is that of
     * the plain eager run.
     */
    @ParameterizedTest
    @CsvSource({"LazyFields", "LazyGrowth", "LazyNamed"})
    void unificationAlone(String main) {
        String[] opts = main.equals("LazyFields")
                ? new String[]{"plugins:[" + LazyFieldsPlugin.class.getName() + "]"}
                : new String[0];
        Snapshot eager = run("reflsound", main, OFF, opts);
        assertTrue(!unifiedFieldsSeen(), main + ": unified fields without the option");
        List<String> unifyOpts = new ArrayList<>(List.of(opts));
        unifyOpts.add(UNIFY);
        Snapshot unified = run("reflsound", main, OFF, unifyOpts.toArray(new String[0]));
        if (main.equals("LazyFields")) {
            assertTrue(unifiedFieldsSeen(), main + ": no unified field with the option");
        }
        assertEquals(0, unified.placeholders());
        assertEquals(eager.edges(), unified.edges(), main + ": call edges");
        assertEquals(eager.reached(), unified.reached(), main + ": reachable methods");
    }

    @Test
    void thresholdBelowMinusOneIsRefused() {
        assertRefused(() -> Tests.testPTA(false, "reflsound", "TypeMatch", MEMBERS, LAZY + -2),
                "reflection-members-lazy must be -1 or at least 0");
    }

    /**
     * The inputs of {@link ReflectionTest}, run with string-constant
     * inference. Their PTAAssert checks are not run: some were written for
     * the solar inference or the reflection log, and {@code sizeEquals}
     * counts member objects, which placeholders merge.
     */
    @ParameterizedTest
    @CsvSource({
            "GetMember", "ReflectiveArgsMerge", "ReflectiveAction",
            "LazyHeapModeling", "ArgsRefine", "GetMethods", "UnknownMethodName",
    })
    void upstreamReflectionInputs(String main) {
        compare("reflection", main, 0, NO_ASSERTIONS);
    }

    @Test
    void upstreamReflectionInputContextSensitive() {
        Comparison comparison = compare("reflection", "ReflectiveArgsMergeCS", 0,
                NO_ASSERTIONS, "cs:1-call");
        assertTrue(comparison.lazy().placeholders() > 0);
    }

    /**
     * A value stored into a field of one placeholder is loaded from another
     * placeholder of the same member: only the shared member object fields
     * carry it, as the one concrete member object does.
     */
    @Test
    void memberObjectsShareTheirFields() {
        Comparison comparison = compare("reflsound", "LazyFields", 0,
                "plugins:[" + LazyFieldsPlugin.class.getName() + "]");
        assertTrue(comparison.lazy().placeholders() > 0);
    }

    @Test
    void lazyMembersNeedTheMembersOption() {
        assertRefused(() -> Tests.testPTA(false, "reflsound", "TypeMatch", LAZY + 0),
                "reflection-members-lazy needs");
    }

    private static void assertRefused(Executable run, String message) {
        Throwable thrown = assertThrows(Throwable.class, run);
        assertTrue(Stream.iterate(thrown, t -> t != null, Throwable::getCause)
                        .anyMatch(t -> String.valueOf(t.getMessage()).contains(message)),
                thrown::toString);
    }

    /**
     * @return whether an instance field of the last run hangs on an object
     * standing for the fields of all member objects of one kind
     */
    private static boolean unifiedFieldsSeen() {
        PointerAnalysisResult pta = World.get().getResult(PointerAnalysis.ID);
        return pta.getInstanceFields().stream()
                .map(field -> field.getBase().getObject())
                .anyMatch(obj -> obj instanceof MockObj mock
                        && mock.getDescriptor().string().equals(MEMBER_FIELDS_DESC));
    }

    /**
     * Runs {@code main} at N=0 and lists the call edges and the points-to
     * sets, each set in its own order, the lines sorted.
     */
    private static List<String> rawOutput(String main) {
        Tests.testPTA(false, "reflsound", main, MEMBERS, LAZY + 0);
        PointerAnalysisResult pta = World.get().getResult(PointerAnalysis.ID);
        List<String> lines = new ArrayList<>();
        pta.getCallGraph().edges().forEach(e -> lines.add(e.getKind() + " "
                + e.getCallSite().getContainer() + "[" + e.getCallSite().getIndex() + "] -> "
                + e.getCallee()));
        for (Var var : pta.getVars()) {
            lines.add(var.getMethod() + "/" + var.getName() + " = " + pta.getPointsToSet(var));
        }
        pta.getCSVars().forEach(csVar -> lines.add(csVar + " = " + csVar.getObjects()));
        pta.getInstanceFields().forEach(field -> lines.add(field + " = " + field.getObjects()));
        pta.getArrayIndexes().forEach(index -> lines.add(index + " = " + index.getObjects()));
        lines.sort(null);
        return lines;
    }

    private record Comparison(Snapshot off, Snapshot lazy) {
    }

    private static Comparison compare(String dir, String main, int threshold, String... opts) {
        Snapshot off = run(dir, main, OFF, opts);
        Snapshot lazy = run(dir, main, LAZY + threshold, opts);
        String id = dir + "/" + main + " N=" + threshold;
        assertEquals(0, off.placeholders(), id + ": placeholder with the option off");
        assertEquals(off.edges(), lazy.edges(), id + ": call edges");
        assertEquals(off.reached(), lazy.reached(), id + ": reachable methods");
        assertEquals(off.pointsTo(), lazy.pointsTo(), id + ": expanded points-to sets");
        System.out.println("LAZYEQ " + id
                + " edges=" + off.edges().size()
                + " reached=" + off.reached().size()
                + " vars=" + off.pointsTo().size()
                + " ciEntries=" + off.ciEntries() + "/" + lazy.ciEntries()
                + " pointerEntries=" + off.pointerEntries() + "/" + lazy.pointerEntries()
                + " placeholders=" + lazy.placeholders());
        return new Comparison(off, lazy);
    }

    /**
     * @param ciEntries      the points-to entries of all variables, context
     *                       insensitive, before expansion
     * @param pointerEntries the points-to entries of all context-sensitive
     *                       pointers (variables, instance and static fields,
     *                       array indexes)
     * @param placeholders   the variable entries that are placeholders
     */
    private record Snapshot(Set<String> edges, Set<String> reached,
                            Map<String, Set<String>> pointsTo,
                            long ciEntries, long pointerEntries, long placeholders) {
    }

    private static Snapshot run(String dir, String main, String lazyOption, String... opts) {
        List<String> ptaOpts = new ArrayList<>(List.of(opts));
        ptaOpts.add(MEMBERS);
        ptaOpts.add(lazyOption);
        if (ptaOpts.remove(NO_ASSERTIONS)) {
            // the options of Tests.testPTA without its AssertionChecker
            ptaOpts.addAll(0, List.of("implicit-entries:false", "only-app:true",
                    "distinguish-string-constants:all"));
            Main.main(new String[]{"-cp", PTA_ROOT, "-cp", PTA_ROOT + "/" + dir, "-m", main,
                    "-a", PointerAnalysis.ID + "=" + String.join(";", ptaOpts)});
        } else {
            Tests.testPTA(false, dir, main, ptaOpts.toArray(new String[0]));
        }
        PointerAnalysisResult pta = World.get().getResult(PointerAnalysis.ID);
        CallGraph<Invoke, JMethod> callGraph = pta.getCallGraph();
        Set<String> edges = callGraph.edges()
                .map(e -> e.getKind() + " " + e.getCallSite().getContainer()
                        + "[" + e.getCallSite().getIndex() + "] -> " + e.getCallee())
                .collect(Collectors.toCollection(TreeSet::new));
        Set<String> reached = callGraph.reachableMethods()
                .map(JMethod::toString)
                .collect(Collectors.toCollection(TreeSet::new));
        Map<String, Set<String>> pointsTo = new TreeMap<>();
        long ciEntries = 0;
        long placeholders = 0;
        for (Var var : pta.getVars()) {
            Set<String> objs = new TreeSet<>();
            for (Obj obj : pta.getPointsToSet(var)) {
                ++ciEntries;
                if (LazyMembers.isPlaceholder(obj)) {
                    ++placeholders;
                    LazyMembers.members(obj).forEach(m -> objs.add(memberText(m)));
                } else if (obj instanceof MockObj mock
                        && mock.getDescriptor().string().equals(MEMBER_DESC)
                        && obj.getAllocation() instanceof ClassMember m) {
                    objs.add(memberText(m));
                } else {
                    objs.add(obj.toString());
                }
            }
            String key = var.getMethod() + "/" + var.getName();
            assertTrue(pointsTo.put(key, objs) == null, "duplicate variable " + key);
        }
        long pointerEntries = entries(pta.getCSVars()) + entries(pta.getInstanceFields())
                + entries(pta.getStaticFields()) + entries(pta.getArrayIndexes());
        return new Snapshot(edges, reached, pointsTo, ciEntries, pointerEntries, placeholders);
    }

    private static String memberText(ClassMember member) {
        return "member " + member;
    }

    private static long entries(Collection<? extends Pointer> pointers) {
        long entries = 0;
        for (Pointer pointer : pointers) {
            PointsToSet pts = pointer.getPointsToSet();
            if (pts != null) {
                entries += pts.size();
            }
        }
        return entries;
    }
}
