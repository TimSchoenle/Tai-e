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

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.type.VoidType;

import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * {@link ReceiverTargets#remapKnown} and {@link ReceiverTargets#sortKnown}:
 * a variable that joins a grouping with its keys in other slots keeps the
 * keys of its known slots, and its known slots are ascending and distinct
 * again after the sort.
 */
class ReceiverTargetsTest {

    private static JClass declaringClass;

    @BeforeAll
    static void buildWorld() {
        Main.buildWorld("-cp", "src/test/resources/world", "--input-classes", "Hierarchy");
        declaringClass = World.get().getClassHierarchy().getClass("C");
        assertNotNull(declaringClass);
    }

    private static MethodRef ref(String name) {
        return MethodRef.get(declaringClass, name, List.of(), VoidType.VOID, false);
    }

    /**
     * @return the grouping of {@code objs} by their first letter
     */
    private static ReceiverGroups<String, String> group(String... objs) {
        return ReceiverGroups.group(List.of(objs), o -> o.substring(0, 1));
    }

    private static int[] known(ReceiverTargets.Target target) {
        ReceiverTargets.SlotList known = target.known();
        return Arrays.copyOf(known.slots(), known.count());
    }

    /**
     * The old grouping has the keys b, a, c in slots 0, 1, 2; the joined one
     * a, c, d, b in slots 0, 1, 2, 3. A known slot keeps its key, slots added
     * unordered after the remap (the new key d, a repeated slot) are allowed,
     * and the sort makes each list ascending and distinct.
     */
    @Test
    void remapKeepsTheKeysOfTheKnownSlotsAndSortRestoresTheOrder() {
        ReceiverGroups<String, String> from = group("b1", "a1", "c1");
        ReceiverGroups<String, String> to = group("a1", "c1", "d1", "b1", "a2");
        ReceiverTargets targets = new ReceiverTargets();
        ReceiverTargets.Target bc = targets.add(ref("bc"));
        bc.known().addLast(from.slotOf("b"));
        bc.known().addLast(from.slotOf("c"));
        ReceiverTargets.Target a = targets.add(ref("a"));
        a.known().addLast(from.slotOf("a"));
        ReceiverTargets.Target none = targets.add(ref("none"));

        targets.remapKnown(from, to);

        assertArrayEquals(new int[]{to.slotOf("b"), to.slotOf("c")}, known(bc));
        assertArrayEquals(new int[]{to.slotOf("a")}, known(a));
        assertArrayEquals(new int[]{}, known(none));

        // the new type d of the difference, below b's slot 3
        bc.known().addLast(to.slotOf("d"));
        // a's slot 0 again after a higher one
        a.known().addLast(to.slotOf("b"));
        a.known().addLast(to.slotOf("a"));
        targets.sortKnown();

        assertArrayEquals(new int[]{1, 2, 3}, known(bc));
        assertArrayEquals(new int[]{0, 3}, known(a));
        assertArrayEquals(new int[]{}, known(none));
        // ordered again
        assertThrows(IllegalStateException.class, () -> bc.known().addLast(0));
    }

    /**
     * A known slot whose key the new grouping lacks would lose that key's
     * receivers: the remap refuses it.
     */
    @Test
    void remapRefusesAKeyMissingFromTheNewGrouping() {
        ReceiverGroups<String, String> from = group("a1", "b1");
        ReceiverGroups<String, String> to = group("a1", "c1");
        ReceiverTargets targets = new ReceiverTargets();
        targets.add(ref("b")).known().addLast(from.slotOf("b"));
        assertThrows(IllegalStateException.class, () -> targets.remapKnown(from, to));
    }

    /**
     * Without a remap, a slot below the last one is refused.
     */
    @Test
    void orderedListRefusesALowerSlot() {
        ReceiverTargets targets = new ReceiverTargets();
        ReceiverTargets.Target target = targets.add(ref("t"));
        target.known().addLast(2);
        assertThrows(IllegalStateException.class, () -> target.known().addLast(1));
    }
}
