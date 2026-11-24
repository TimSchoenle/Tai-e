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

import org.jspecify.annotations.Nullable;
import pascal.taie.util.collection.Maps;

import java.util.Arrays;
import java.util.Map;
import java.util.Objects;

/**
 * Objects grouped by a key, keys and the objects of each key in first-seen
 * order. Add-only. Most groups hold one object, so a group of one object is
 * held as the object itself; a second object of the key turns it into a
 * list.
 *
 * @param <K> type of keys
 * @param <V> type of objects
 */
final class ReceiverGroups<K, V> {

    /**
     * Value: the group's only object, or a {@link Group} of two or more.
     * {@link Group} is private, so no object can be mistaken for a group.
     */
    private final Map<K, Object> groups = Maps.newLinkedHashMap();

    /**
     * Adds {@code obj} at the end of the group of {@code key}.
     */
    void add(K key, V obj) {
        Objects.requireNonNull(obj);
        Object group = groups.putIfAbsent(key, obj);
        if (group == null) {
            return;
        }
        if (group instanceof Group list) {
            list.add(obj);
        } else {
            // replacing the value of a present key keeps its position
            groups.put(key, new Group(group, obj));
        }
    }

    /**
     * Appends the groups of {@code more} in place: a group of a new key comes
     * after the existing keys, held as its object or copied into an exactly
     * sized list; the objects of a known key come after that key's objects.
     * Nothing of {@code more} is shared.
     */
    void appendAll(ReceiverGroups<K, V> more) {
        more.groups.forEach((key, extra) -> {
            Object group = groups.get(key);
            if (group == null) {
                groups.put(key, extra instanceof Group list ? list.copy() : extra);
            } else if (group instanceof Group list) {
                list.addAll(extra);
            } else {
                Group list = new Group(1 + sizeOf(extra));
                list.add(group);
                list.addAll(extra);
                groups.put(key, list);
            }
        });
    }

    /**
     * Visits the groups: per key, {@link #enter} once, then {@link #accept}
     * per object with the state {@code enter} returned.
     *
     * @param <K> type of keys
     * @param <V> type of objects
     * @param <S> type of the per-key state
     */
    interface Visitor<K, V, S> {

        /**
         * @return the state passed to {@link #accept} for the objects of
         * {@code key}, or null to skip the key.
         */
        @Nullable
        S enter(K key);

        void accept(S state, V obj);
    }

    /**
     * For each key in first-seen order, calls {@code visitor.enter} and, if
     * it returns a state, {@code visitor.accept} for each object of the key
     * in first-seen order.
     */
    @SuppressWarnings("unchecked")
    <S> void forEachGroup(Visitor<? super K, ? super V, S> visitor) {
        for (Map.Entry<K, Object> entry : groups.entrySet()) {
            S state = visitor.enter(entry.getKey());
            if (state == null) {
                continue;
            }
            Object group = entry.getValue();
            if (group instanceof Group list) {
                for (int i = 0; i < list.size; ++i) {
                    visitor.accept(state, (V) list.elements[i]);
                }
            } else {
                visitor.accept(state, (V) group);
            }
        }
    }

    /**
     * @return the number of keys.
     */
    int keyCount() {
        return groups.size();
    }

    /**
     * @return the number of objects over all keys.
     */
    long objectCount() {
        long count = 0;
        for (Object group : groups.values()) {
            count += sizeOf(group);
        }
        return count;
    }

    /**
     * @return the object of {@code key} if it is held as a single object
     * (not in a list), otherwise null. For tests of the representation.
     */
    @Nullable
    @SuppressWarnings("unchecked")
    V singleObject(K key) {
        Object group = groups.get(key);
        return group instanceof Group ? null : (V) group;
    }

    /**
     * @return the number of slots of {@code key}'s list, or -1 if the key
     * holds a single object or is absent. For tests of the representation.
     */
    int listCapacity(K key) {
        return groups.get(key) instanceof Group list ? list.elements.length : -1;
    }

    private static int sizeOf(Object group) {
        return group instanceof Group list ? list.size : 1;
    }

    /**
     * An append-only list of two or more objects.
     */
    private static final class Group {

        private Object[] elements;

        private int size;

        private Group(int capacity) {
            elements = new Object[capacity];
        }

        private Group(Object first, Object second) {
            elements = new Object[]{first, second};
            size = 2;
        }

        private void add(Object obj) {
            if (size == elements.length) {
                // the growth of java.util.ArrayList
                elements = Arrays.copyOf(elements, size + Math.max(1, size >> 1));
            }
            elements[size++] = obj;
        }

        /**
         * Appends {@code group}: one object or the objects of a list.
         */
        private void addAll(Object group) {
            if (group instanceof Group list) {
                int needed = size + list.size;
                if (needed > elements.length) {
                    elements = Arrays.copyOf(elements,
                            Math.max(needed, elements.length + (elements.length >> 1)));
                }
                System.arraycopy(list.elements, 0, elements, size, list.size);
                size = needed;
            } else {
                add(group);
            }
        }

        private Group copy() {
            Group copy = new Group(size);
            System.arraycopy(elements, 0, copy.elements, 0, size);
            copy.size = size;
            return copy;
        }
    }
}
