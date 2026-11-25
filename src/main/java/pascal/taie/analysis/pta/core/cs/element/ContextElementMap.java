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

package pascal.taie.analysis.pta.core.cs.element;

import org.jspecify.annotations.Nullable;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.util.collection.HybridHashMap;
import pascal.taie.util.collection.Maps;

import java.util.AbstractCollection;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Set;

/**
 * Map from a key and a context to the context-sensitive element of that key
 * in that context, with no map object per key.
 * <p>
 * The slot of a key holds the element itself while the key has one context,
 * an array of up to {@link #SMALL_SIZE} elements in insertion order, and a
 * {@link HashMap} from context to element beyond that. These are the three
 * shapes {@link HybridHashMap} takes (singleton, small array map, hash map),
 * filled by the same operations in the same order, so every iteration order
 * of this map equals that of {@link Maps#newTwoKeyMap()} filled with the same
 * sequence of insertions: keys in the order of the outer {@link HashMap}, and
 * the elements of a key in insertion order up to {@link #SMALL_SIZE} contexts,
 * in the order of its context {@link HashMap} beyond.
 * <p>
 * Elements are never removed.
 *
 * @param <K> type of the keys
 * @param <E> type of the elements
 */
final class ContextElementMap<K, E extends CSElement> {

    /**
     * Number of contexts up to which a key keeps its elements in an array;
     * equals the threshold of {@link HybridHashMap}.
     */
    static final int SMALL_SIZE = 8;

    /**
     * Initial capacity of the context map of a key with more than
     * {@link #SMALL_SIZE} contexts; equals the one {@link HybridHashMap}
     * gives its hash map.
     */
    private static final int LARGE_INITIAL_CAPACITY = SMALL_SIZE * 2;

    /**
     * Slot of each key: an element, an {@code Object[]} of elements
     * (unused entries at the end are null), or a
     * {@code HashMap<Context, E>}.
     */
    private final Map<K, Object> slots = Maps.newMap();

    /**
     * Number of elements in this map.
     */
    private int size = 0;

    /**
     * @return the element of {@code key} in {@code context},
     * or null if there is none.
     */
    @Nullable E get(K key, Context context) {
        Object slot = slots.get(key);
        if (slot == null) {
            return null;
        }
        if (slot instanceof Object[] small) {
            for (Object o : small) {
                if (o == null) {
                    return null;
                }
                E element = cast(o);
                if (element.getContext().equals(context)) {
                    return element;
                }
            }
            return null;
        }
        if (slot instanceof HashMap<?, ?> large) {
            return cast(large.get(context));
        }
        E element = cast(slot);
        return element.getContext().equals(context) ? element : null;
    }

    /**
     * Adds {@code element} under {@code key} and the context of
     * {@code element}. The caller ensures that {@code key} has no element
     * in that context yet.
     */
    void add(K key, E element) {
        Context context = Objects.requireNonNull(element.getContext(),
                "context of a context-sensitive element");
        Objects.requireNonNull(key, "key of a context-sensitive element");
        // one computeIfAbsent per added element, as MapMapTwoKeyMap calls on
        // its outer map: HashMap links a new key first in its bin there (last
        // by put), and resizes there before the call once the size passed the
        // threshold, also for a present key; both decide the key order
        Object slot = slots.computeIfAbsent(key, k -> element);
        if (slot == element) {
            ++size;
            return;
        }
        if (slot instanceof Object[] small) {
            int n = count(small);
            if (n < small.length) {
                small[n] = element;
            } else if (n < SMALL_SIZE) {
                Object[] grown = Arrays.copyOf(small, Math.min(n * 2, SMALL_SIZE));
                grown[n] = element;
                slots.put(key, grown);
            } else {
                HashMap<Context, E> large = new HashMap<>(LARGE_INITIAL_CAPACITY);
                for (Object o : small) {
                    E e = cast(o);
                    large.put(e.getContext(), e);
                }
                large.put(context, element);
                slots.put(key, large);
            }
        } else if (slot instanceof HashMap<?, ?> large) {
            HashMap<Context, E> contextMap = cast(large);
            contextMap.put(context, element);
        } else {
            slots.put(key, new Object[]{ slot, element });
        }
        ++size;
    }

    /**
     * @return the keys that have an element, in the order of the outer map.
     */
    Set<K> keySet() {
        return Collections.unmodifiableSet(slots.keySet());
    }

    /**
     * @return the elements of {@code key} at the time of the call.
     */
    Collection<E> valuesOf(K key) {
        Object slot = slots.get(key);
        if (slot == null) {
            return Set.of();
        }
        if (slot instanceof Object[] small) {
            List<E> elements = cast(Arrays.asList(Arrays.copyOf(small, count(small))));
            return Collections.unmodifiableList(elements);
        }
        if (slot instanceof HashMap<?, ?> large) {
            HashMap<Context, E> contextMap = cast(large);
            return List.copyOf(contextMap.values());
        }
        E element = cast(slot);
        return List.of(element);
    }

    /**
     * @return a view of all elements, key by key in the order of the outer
     * map. Elements must not be added while the view is iterated.
     */
    Collection<E> values() {
        return new AbstractCollection<>() {
            @Override
            public Iterator<E> iterator() {
                return new ValueIterator();
            }

            @Override
            public int size() {
                return size;
            }
        };
    }

    private static int count(Object[] small) {
        int n = 0;
        while (n < small.length && small[n] != null) {
            ++n;
        }
        return n;
    }

    @SuppressWarnings("unchecked")
    private static <T> T cast(Object o) {
        return (T) o;
    }

    /**
     * Iterates the elements key by key in the order of the outer map.
     */
    private final class ValueIterator implements Iterator<E> {

        private final Iterator<Object> slotIt = slots.values().iterator();

        /**
         * Elements of the current slot not yet returned, or null.
         */
        private @Nullable Iterator<?> elementIt;

        /**
         * The current slot if it is a single element not yet returned, or null.
         */
        private @Nullable Object single;

        @Override
        public boolean hasNext() {
            while (single == null && (elementIt == null || !elementIt.hasNext())) {
                if (!slotIt.hasNext()) {
                    return false;
                }
                Object slot = slotIt.next();
                elementIt = null;
                if (slot instanceof Object[] small) {
                    elementIt = Arrays.asList(small).subList(0, count(small)).iterator();
                } else if (slot instanceof HashMap<?, ?> large) {
                    elementIt = large.values().iterator();
                } else {
                    single = slot;
                }
            }
            return true;
        }

        @Override
        public E next() {
            if (!hasNext()) {
                throw new NoSuchElementException();
            }
            if (single != null) {
                E element = cast(single);
                single = null;
                return element;
            }
            return cast(Objects.requireNonNull(elementIt).next());
        }
    }
}
