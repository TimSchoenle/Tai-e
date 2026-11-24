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
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.language.type.IntType;
import pascal.taie.language.type.VoidType;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * {@link ClassHierarchyImpl#dispatch(JClass, MethodRef)} looks a receiver
 * class and subsignature up once, whether the lookup finds a method or not.
 * The receiver class equals the declaring class of each reference, so the
 * subclass check needs no class added to the counting hierarchy.
 */
class DispatchCacheTest {

    /**
     * Counts the uncached lookups of {@link ClassHierarchyImpl#dispatch}.
     */
    private static final class CountingHierarchy extends ClassHierarchyImpl {

        private int lookups;

        @Override
        JMethod lookupDispatchTarget(JClass receiverClass, Subsignature subsignature) {
            ++lookups;
            return super.lookupDispatchTarget(receiverClass, subsignature);
        }
    }

    @BeforeAll
    static void buildWorld() {
        Main.buildWorld("-cp", "src/test/resources/world", "--input-classes", "Hierarchy");
    }

    @Test
    void missIsLookedUpOnce() {
        JClass c = World.get().getClassHierarchy().getClass("C");
        assertNotNull(c);
        MethodRef absent = MethodRef.get(c, "noSuchMethod", List.of(), VoidType.VOID, false);
        CountingHierarchy hierarchy = new CountingHierarchy();
        assertNull(hierarchy.dispatch(c, absent));
        assertNull(hierarchy.dispatch(c, absent));
        assertNull(hierarchy.dispatch(c, absent));
        assertEquals(1, hierarchy.lookups);
    }

    @Test
    void hitIsLookedUpOnce() {
        JClass string = World.get().getClassHierarchy().getJREClass("java.lang.String");
        assertNotNull(string);
        MethodRef length = MethodRef.get(string, "length", List.of(), IntType.INT, false);
        CountingHierarchy hierarchy = new CountingHierarchy();
        JMethod first = hierarchy.dispatch(string, length);
        assertNotNull(first);
        assertEquals(string, first.getDeclaringClass());
        assertSame(first, hierarchy.dispatch(string, length));
        assertEquals(1, hierarchy.lookups);
    }
}
