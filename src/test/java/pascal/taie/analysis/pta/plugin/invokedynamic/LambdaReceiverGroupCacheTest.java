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

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link ReceiverGroupCache}: variables holding one set object hold one
 * grouping; a grouping is used for a set only when it holds as many
 * objects; the last holder takes an entry out of the table.
 */
class LambdaReceiverGroupCacheTest {

    /**
     * @return the grouping of {@code objs} by their first letter
     */
    private static ReceiverGroups<String, String> group(String... objs) {
        return ReceiverGroups.group(List.of(objs), o -> o.substring(0, 1));
    }

    private static Supplier<ReceiverGroups<String, String>> grouper(String... objs) {
        return () -> group(objs);
    }

    /**
     * @return the objects of {@code groups} in visiting order
     */
    private static List<String> objects(ReceiverGroups<String, String> groups) {
        List<String> out = new ArrayList<>();
        groups.forEachGroup(new ReceiverGroups.Visitor<String, String, Object>() {
            @Override
            public Object enter(String key) {
                return key;
            }

            @Override
            public void accept(Object state, String obj) {
                out.add(obj);
            }
        });
        return out;
    }

    @Test
    void twoVariablesWithOneSetHoldOneGrouping() {
        ReceiverGroupCache<String, String> cache = new ReceiverGroupCache<>(true);
        Object set = new Object();
        ReceiverGroupCache.Entry<String, String> a = cache.attach(set, 2, grouper("a1", "b1"));
        ReceiverGroupCache.Entry<String, String> b = cache.attach(set, 2, grouper("a1", "b1"));
        assertSame(a, b);
        assertEquals(2, ReceiverGroupCache.holders(a));
        assertEquals(1, cache.size());
    }

    @Test
    void unsharedVariablesHoldTheirOwnGroupings() {
        ReceiverGroupCache<String, String> cache = new ReceiverGroupCache<>(false);
        Object set = new Object();
        ReceiverGroupCache.Entry<String, String> a = cache.attach(set, 2, grouper("a1", "b1"));
        ReceiverGroupCache.Entry<String, String> b = cache.attach(set, 2, grouper("a1", "b1"));
        assertNotSame(a, b);
        assertEquals(0, cache.size());
    }

    /**
     * The solver changes a set held by one pointer in place: a grouping of
     * the set's smaller content is not used for it.
     */
    @Test
    void aGroupingOfFewerObjectsIsNotUsed() {
        ReceiverGroupCache<String, String> cache = new ReceiverGroupCache<>(true);
        Object set = new Object();
        ReceiverGroupCache.Entry<String, String> a = cache.attach(set, 1, grouper("a1"));
        ReceiverGroupCache.Entry<String, String> b = cache.attach(set, 2, grouper("a1", "b1"));
        assertNotSame(a, b);
        assertEquals(List.of("a1", "b1"), objects(b.groups()));
        assertEquals(List.of("a1"), objects(a.groups()));
    }

    @Test
    void aSoleHolderExtendsInPlaceAndTheLastHolderFreesTheEntry() {
        ReceiverGroupCache<String, String> cache = new ReceiverGroupCache<>(true);
        Object s1 = new Object();
        Object s2 = new Object();
        ReceiverGroupCache.Entry<String, String> a = cache.attach(s1, 1, grouper("a1"));
        ReceiverGroupCache.Advance<String, String> next =
                cache.advance(a, s2, 2, group("b1"), 1, grouper("a1", "b1"));
        assertSame(a, next.entry());
        assertTrue(next.slotsKept());
        assertEquals(List.of("a1", "b1"), objects(a.groups()));
        assertEquals(1, cache.size());
        // a new variable with the old set object, now grown, finds nothing
        ReceiverGroupCache.Entry<String, String> c = cache.attach(s1, 3,
                grouper("a1", "b1", "c1"));
        assertNotSame(a, c);
        // the variable joins the grouping of another set object; its own
        // entry, held by no variable, leaves the table
        ReceiverGroupCache.Advance<String, String> joined =
                cache.advance(a, s1, 3, group("c1"), 1, grouper("a1", "b1", "c1"));
        assertSame(c, joined.entry());
        assertFalse(joined.slotsKept());
        assertEquals(1, cache.size());
        assertEquals(2, ReceiverGroupCache.holders(c));
    }

    @Test
    void aSharedGroupingIsCopiedNotChanged() {
        ReceiverGroupCache<String, String> cache = new ReceiverGroupCache<>(true);
        Object s1 = new Object();
        Object s2 = new Object();
        ReceiverGroupCache.Entry<String, String> a = cache.attach(s1, 1, grouper("a1"));
        cache.attach(s1, 1, grouper("a1"));
        ReceiverGroupCache.Advance<String, String> next =
                cache.advance(a, s2, 2, group("b1"), 1, grouper("a1", "b1"));
        assertNotSame(a, next.entry());
        assertTrue(next.slotsKept());
        assertEquals(List.of("a1"), objects(a.groups()));
        assertEquals(List.of("a1", "b1"), objects(next.entry().groups()));
        assertEquals(1, ReceiverGroupCache.holders(a));
        assertEquals(2, cache.size());
    }

    /**
     * A grouping made while the variable's set was being propagated holds
     * the difference already: it is not appended twice.
     */
    @Test
    void aGroupingMadeInsideTheWindowIsNotExtendedTwice() {
        ReceiverGroupCache<String, String> cache = new ReceiverGroupCache<>(true);
        Object set = new Object();
        ReceiverGroupCache.Entry<String, String> a = cache.attach(set, 2, grouper("a1", "b1"));
        ReceiverGroupCache.Advance<String, String> next =
                cache.advance(a, set, 2, group("b1"), 1, grouper("a1", "b1"));
        assertSame(a, next.entry());
        assertTrue(next.slotsKept());
        assertEquals(List.of("a1", "b1"), objects(a.groups()));
    }

    /**
     * Neither count fits (the solver broke its propagation order): the
     * grouping is made anew from the set.
     */
    @Test
    void anUnexpectedCountRegroupsTheSet() {
        ReceiverGroupCache<String, String> cache = new ReceiverGroupCache<>(true);
        Object s1 = new Object();
        Object s2 = new Object();
        ReceiverGroupCache.Entry<String, String> a = cache.attach(s1, 1, grouper("a1"));
        ReceiverGroupCache.Advance<String, String> next =
                cache.advance(a, s2, 3, group("b1"), 1, grouper("a1", "b1", "c1"));
        assertFalse(next.slotsKept());
        assertEquals(List.of("a1", "b1", "c1"), objects(next.entry().groups()));
        assertEquals(1, cache.size());
    }

    @Test
    void unsharedAppendsAsBefore() {
        ReceiverGroupCache<String, String> cache = new ReceiverGroupCache<>(false);
        Object set = new Object();
        ReceiverGroupCache.Entry<String, String> a = cache.attach(set, 2, grouper("a1", "b1"));
        ReceiverGroupCache.Advance<String, String> next =
                cache.advance(a, set, 2, group("b1"), 1, grouper("a1", "b1"));
        assertSame(a, next.entry());
        // without sharing, a grouping made inside the window lists the
        // difference twice, as the per-variable grouping always did
        assertEquals(List.of("a1", "b1", "b1"), objects(a.groups()));
    }
}
