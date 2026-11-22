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

package pascal.taie.language.classes;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.World;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks {@link ClassHierarchy#isSubclass} against the walk it replaced, over every ordered pair of a small
 * hierarchy: the classes of {@code Hierarchy.java} (interfaces with multiple super-interfaces, abstract classes
 * implementing them, a class chain) and a few JDK classes whose interfaces are reached along several paths.
 */
class SubtypeIndexTest {

    private static final String[] CLASS_NAMES = {
            "Hierarchy", "I", "II", "III", "IIII", "C", "D", "E", "F", "G", "H",
            "java.lang.Object", "java.lang.String", "java.lang.CharSequence", "java.lang.Comparable",
            "java.io.Serializable", "java.lang.Iterable", "java.util.Collection", "java.util.List",
            "java.util.AbstractCollection", "java.util.AbstractList", "java.util.ArrayList",
            "java.util.RandomAccess",
    };

    @BeforeAll
    static void buildWorld() {
        Main.buildWorld("-cp", "src/test/resources/world", "--input-classes", "Hierarchy");
    }

    @Test
    void everyPairAgreesWithTheSubclassWalk() {
        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        List<JClass> classes = new ArrayList<>();
        for (String name : CLASS_NAMES) {
            JClass c = hierarchy.getClass(name);
            assertNotNull(c, name);
            classes.add(c);
        }
        JClass object = hierarchy.getJREClass("java.lang.Object");
        List<String> mismatches = new ArrayList<>();
        int yes = 0;
        for (JClass sup : classes) {
            for (JClass sub : classes) {
                boolean walked = sup.equals(sub) || sup == object
                        || hierarchy.getAllSubclassesOf(sup).contains(sub);
                boolean answered = hierarchy.isSubclass(sup, sub);
                if (walked != answered) {
                    mismatches.add(sup + " :> " + sub + " walk=" + walked + " isSubclass=" + answered);
                }
                if (walked) {
                    yes++;
                }
            }
        }
        assertEquals(List.of(), mismatches);
        // both answers occur, so the comparison is not vacuous
        int pairs = classes.size() * classes.size();
        assertTrue(yes > classes.size() && yes < pairs, "subclass pairs " + yes + " of " + pairs);
    }
}
