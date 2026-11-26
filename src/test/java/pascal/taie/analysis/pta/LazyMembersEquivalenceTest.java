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

    @ParameterizedTest
    @CsvSource({
            "reflsound, TypeMatch, 0", "reflsound, ArgTypes, 0",
            "reflsound, GetMethodIface, 0", "reflsound, MemberArrays, 0",
            "reflsound, ClassInit, 0", "reflsound, LazyGrowth, 0",
            "reflsound, LazyGrowth, 1", "reflsound, MemberArrays, 1",
    })
    void reflectionSoundnessFixtures(String dir, String main, int threshold) {
        Comparison comparison = compare(dir, main, threshold);
        // at N=1 a call site with one receiver class keeps it eager
        if (threshold == 0 || main.equals("LazyGrowth")) {
            assertTrue(comparison.lazy().placeholders() > 0,
                    main + " holds no placeholder at N=" + threshold);
        }
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
        Throwable thrown = assertThrows(Throwable.class,
                () -> Tests.testPTA(false, "reflsound", "TypeMatch", LAZY + 0));
        assertTrue(Stream.iterate(thrown, t -> t != null, Throwable::getCause)
                        .anyMatch(t -> String.valueOf(t.getMessage())
                                .contains("reflection-members-lazy needs")),
                thrown::toString);
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
