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

package pascal.taie.analysis.pta.plugin.reflection;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.ClassNames;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks that {@link MemberReceiverIndex} visits exactly the (member,
 * receiver) pairs whose receiver type is a subclass of the member's
 * declaring class in the relation {@code ClassHierarchy.isSubclass} answers
 * (the check of {@code ClassHierarchy.dispatch}), each pair once in any
 * arrival order, with work linear in the deltas, over the classes of
 * {@code Hierarchy.java} ({@code D extends C}, {@code E extends C implements
 * I, II}, {@code III extends I, II}).
 */
class MemberReceiverIndexTest {

    private record Member(int id, JClass declaringClass) {
    }

    private record Receiver(int id, Type type) {
    }

    private record Pair(Member member, Receiver receiver) {
    }

    @BeforeAll
    static void buildWorld() {
        Main.buildWorld("-cp", "src/test/resources/world", "--input-classes", "Hierarchy");
    }

    @Test
    void visitsExactlyTheSubclassPairsOnceInAnyOrder() {
        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        List<JClass> classes = List.of(cls(hierarchy, "C"), cls(hierarchy, "D"),
                cls(hierarchy, "E"), cls(hierarchy, "I"), cls(hierarchy, "II"),
                cls(hierarchy, "III"), cls(hierarchy, ClassNames.OBJECT));
        List<Member> members = new ArrayList<>();
        List<Receiver> receivers = new ArrayList<>();
        for (JClass jclass : classes) {
            members.add(new Member(members.size(), jclass));
            receivers.add(new Receiver(receivers.size(), jclass.getType()));
            receivers.add(new Receiver(receivers.size(), jclass.getType()));
        }
        Set<Pair> expected = new HashSet<>();
        for (Member m : members) {
            for (Receiver r : receivers) {
                JClass receiverClass = ((ClassType) r.type()).getJClass();
                if (hierarchy.isSubclass(m.declaringClass(), receiverClass)) {
                    expected.add(new Pair(m, r));
                }
            }
        }
        // members first, receivers first, and interleaved one by one
        for (int order = 0; order < 3; order++) {
            List<Pair> visited = new ArrayList<>();
            MemberReceiverIndex<Member, Receiver> index = newIndex(hierarchy);
            MemberReceiverIndex.PairAction<Member, Receiver> action = (m, type, rs) -> {
                for (Receiver r : rs) {
                    assertEquals(type, r.type());
                    visited.add(new Pair(m, r));
                }
            };
            if (order == 0) {
                members.forEach(m -> index.addMember(m, action));
                index.addReceivers(receivers, action);
            } else if (order == 1) {
                index.addReceivers(receivers, action);
                members.forEach(m -> index.addMember(m, action));
            } else {
                for (int i = 0; i < receivers.size(); i++) {
                    index.addReceivers(List.of(receivers.get(i)), action);
                    if (i < members.size()) {
                        index.addMember(members.get(i), action);
                    }
                }
            }
            // a second delivery of everything adds no pair
            members.forEach(m -> index.addMember(m, action));
            index.addReceivers(receivers, action);
            assertEquals(expected, new HashSet<>(visited), "order " + order);
            assertEquals(expected.size(), visited.size(), "each pair once, order " + order);
        }
    }

    /**
     * The cost shape of the 26.2 stall: a pool of many Method objects and
     * many receivers, arriving one by one in both handler arguments. The
     * old handler crossed the whole other set on every delta; the index
     * does one unit per object given and one per pair it creates.
     */
    @Test
    void workIsLinearInTheDeltas() {
        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JClass c = cls(hierarchy, "C");
        List<JClass> others = List.of(cls(hierarchy, "I"), cls(hierarchy, "II"),
                cls(hierarchy, "III"), cls(hierarchy, "IIII"));
        Type d = cls(hierarchy, "D").getType();
        int nMembers = 32_000;
        int nReceivers = 1_000;
        List<Member> members = new ArrayList<>();
        int compatible = 0;
        for (int i = 0; i < nMembers; i++) {
            // one member in a hundred is declared in C, a superclass of D
            JClass declaringClass = i % 100 == 0 ? c : others.get(i % others.size());
            members.add(new Member(i, declaringClass));
            if (declaringClass == c) {
                compatible++;
            }
        }
        List<Receiver> receivers = new ArrayList<>();
        for (int i = 0; i < nReceivers; i++) {
            receivers.add(new Receiver(i, d));
        }

        // the old handler: every delta crosses the whole other side
        long naiveStart = System.nanoTime();
        long naivePairs = 0;
        long naiveEdges = 0;
        List<Member> seenMembers = new ArrayList<>();
        List<Receiver> seenReceivers = new ArrayList<>();
        JClass dClass = ((ClassType) d).getJClass();
        // the index's work, unit by unit: an object given (1); for the
        // first receiver of a type, its closure registered; for each
        // receiver delta, its closure walked and one visit per compatible
        // member known; for a compatible member, one visit of type D once
        // a receiver is known
        int closure = new SupertypeClosure(hierarchy).of(d).size();
        long expectedWork = 0;
        long compatibleSeen = 0;
        for (int step = 0; step < nMembers + nReceivers; step++) {
            boolean memberDelta = step % 33 != 32 || seenReceivers.size() == nReceivers;
            if (memberDelta && seenMembers.size() < nMembers) {
                Member m = members.get(seenMembers.size());
                seenMembers.add(m);
                expectedWork++;
                if (m.declaringClass() == c) {
                    compatibleSeen++;
                    if (!seenReceivers.isEmpty()) {
                        expectedWork++;
                    }
                }
                for (Receiver ignored : seenReceivers) {
                    naivePairs++;
                    if (hierarchy.isSubclass(m.declaringClass(), dClass)) {
                        naiveEdges++;
                    }
                }
            } else if (seenReceivers.size() < nReceivers) {
                Receiver r = receivers.get(seenReceivers.size());
                expectedWork += 1 + (seenReceivers.isEmpty() ? closure : 0)
                        + closure + compatibleSeen;
                seenReceivers.add(r);
                for (Member m : seenMembers) {
                    naivePairs++;
                    if (hierarchy.isSubclass(m.declaringClass(), dClass)) {
                        naiveEdges++;
                    }
                }
            }
        }
        long naiveNanos = System.nanoTime() - naiveStart;

        long indexStart = System.nanoTime();
        MemberReceiverIndex<Member, Receiver> index = newIndex(hierarchy);
        long[] edges = new long[1];
        MemberReceiverIndex.PairAction<Member, Receiver> action =
                (m, type, rs) -> edges[0] += rs.size();
        int givenMembers = 0;
        int givenReceivers = 0;
        for (int step = 0; step < nMembers + nReceivers; step++) {
            boolean memberDelta = step % 33 != 32 || givenReceivers == nReceivers;
            if (memberDelta && givenMembers < nMembers) {
                index.addMember(members.get(givenMembers++), action);
            } else if (givenReceivers < nReceivers) {
                index.addReceivers(List.of(receivers.get(givenReceivers++)), action);
            }
        }
        long indexNanos = System.nanoTime() - indexStart;

        long pairs = (long) compatible * nReceivers;
        assertEquals(pairs, naiveEdges);
        assertEquals(pairs, edges[0]);
        assertEquals(expectedWork, index.work());
        assertTrue(naivePairs > 10 * index.work(),
                "old shape " + naivePairs + " vs index " + index.work());
        System.out.printf("MemberReceiverIndexTest: old shape %d pair checks in %d ms,"
                        + " index work %d in %d ms%n",
                naivePairs, naiveNanos / 1_000_000, index.work(), indexNanos / 1_000_000);
    }

    @Test
    void closureIsTheSubclassRelationOfDispatch() {
        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        SupertypeClosure closure = new SupertypeClosure(hierarchy);
        List<JClass> classes = hierarchy.applicationClasses().toList();
        assertTrue(classes.size() > 5, classes.toString());
        for (JClass receiver : classes) {
            List<JClass> supertypes = closure.of(receiver.getType());
            for (JClass declaring : classes) {
                assertEquals(hierarchy.isSubclass(declaring, receiver),
                        supertypes.contains(declaring), declaring + " / " + receiver);
            }
            assertTrue(supertypes.contains(cls(hierarchy, ClassNames.OBJECT)), receiver.toString());
        }
        // an array dispatches as Object
        Type array = World.get().getTypeSystem()
                .getArrayType(cls(hierarchy, "C").getType(), 1);
        assertEquals(List.of(cls(hierarchy, ClassNames.OBJECT)), closure.of(array));
    }

    private static MemberReceiverIndex<Member, Receiver> newIndex(ClassHierarchy hierarchy) {
        return new MemberReceiverIndex<>(new SupertypeClosure(hierarchy),
                Member::declaringClass, Receiver::type);
    }

    private static JClass cls(ClassHierarchy hierarchy, String name) {
        JClass jclass = hierarchy.getClass(name);
        assertNotNull(jclass, name);
        return jclass;
    }
}
