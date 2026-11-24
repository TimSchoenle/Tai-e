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

package pascal.taie.util.collection;

import java.util.AbstractSet;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Objects;

/**
 * Add-only set that stores its elements in one array, without a node per
 * element. Up to {@link #SMALL_LIMIT} elements the array is dense and kept
 * in insertion order (searched linearly, as {@link ArraySet} does); past
 * that it becomes an open-addressing table with linear probing on the
 * elements' {@code hashCode}, compared by {@code equals}. Membership
 * follows {@code equals}/{@code hashCode} exactly as {@link java.util.HashSet}
 * does. Elements cannot be removed and must be non-null.
 */
public final class OpenHashSet<E> extends AbstractSet<E> {

    /**
     * Largest size kept as a dense insertion-ordered array; equal to the
     * small-set threshold of {@link AbstractHybridSet}, so a set of at most
     * this many elements iterates in the order the hybrid set does.
     */
    public static final int SMALL_LIMIT = 8;

    private static final Object[] EMPTY = {};

    private Object[] table = EMPTY;

    /**
     * The only element while {@code size == 1} and {@code table} is
     * {@link #EMPTY} (no array for a one-element set, as the hybrid set
     * keeps its singleton); null otherwise.
     */
    private Object single;

    private int size;

    /** Count of successful adds, to fail fast on an add during iteration. */
    private int modCount;

    @Override
    public boolean add(E e) {
        Objects.requireNonNull(e, "OpenHashSet does not permit null");
        if (table == EMPTY) {
            if (size == 0) {
                single = e;
            } else if (single.equals(e)) {
                return false;
            } else {
                table = new Object[] {single, e};
                single = null;
            }
            ++size;
            ++modCount;
            return true;
        }
        int slot;
        if (isDense()) {
            if (containsDense(e)) {
                return false;
            }
            if (size < SMALL_LIMIT) {
                if (size == table.length) {
                    Object[] grown = new Object[Math.max(1, Math.min(SMALL_LIMIT, size * 2))];
                    System.arraycopy(table, 0, grown, 0, size);
                    table = grown;
                }
                table[size++] = e;
                ++modCount;
                return true;
            }
            rehash(SMALL_LIMIT * 2);
            slot = findSlot(table, e);
        } else {
            slot = findSlot(table, e);
            if (table[slot] != null) {
                return false;
            }
            if ((size + 1) * 3L > table.length * 2L) {
                rehash(table.length * 2);
                slot = findSlot(table, e);
            }
        }
        table[slot] = e;
        ++size;
        ++modCount;
        return true;
    }

    /**
     * The array is dense (insertion-ordered, no gaps before {@code size})
     * exactly while its length is at most {@link #SMALL_LIMIT}; every hash
     * table is at least twice that long.
     */
    private boolean isDense() {
        return table.length <= SMALL_LIMIT;
    }

    private boolean containsDense(Object o) {
        for (int i = 0; i < size; ++i) {
            if (table[i].equals(o)) {
                return true;
            }
        }
        return false;
    }

    private void rehash(int capacity) {
        Object[] old = table;
        Object[] fresh = new Object[capacity];
        for (Object o : old) {
            if (o != null) {
                fresh[findSlot(fresh, o)] = o;
            }
        }
        table = fresh;
    }

    /**
     * @return the slot holding an element equal to {@code o}, or the empty
     * slot where it would be stored.
     */
    private static int findSlot(Object[] tab, Object o) {
        int h = o.hashCode();
        int mask = tab.length - 1;
        int i = (h ^ (h >>> 16)) & mask;
        Object cur;
        while ((cur = tab[i]) != null && !cur.equals(o)) {
            i = (i + 1) & mask;
        }
        return i;
    }

    @Override
    public boolean contains(Object o) {
        if (o == null || size == 0) {
            return false;
        }
        if (table == EMPTY) {
            return single.equals(o);
        }
        if (isDense()) {
            return containsDense(o);
        }
        return table[findSlot(table, o)] != null;
    }

    @Override
    public int size() {
        return size;
    }

    @Override
    public Iterator<E> iterator() {
        return new Iterator<>() {

            private final int expectedModCount = modCount;

            private final Object[] tab = table;

            /** The single element not yet returned, if any. */
            private Object pendingSingle = tab == EMPTY ? single : null;

            private int index = advance(0);

            private int advance(int from) {
                int i = from;
                while (i < tab.length && tab[i] == null) {
                    ++i;
                }
                return i;
            }

            @Override
            public boolean hasNext() {
                return pendingSingle != null || index < tab.length;
            }

            @Override
            @SuppressWarnings("unchecked")
            public E next() {
                if (modCount != expectedModCount) {
                    throw new ConcurrentModificationException();
                }
                if (pendingSingle != null) {
                    E e = (E) pendingSingle;
                    pendingSingle = null;
                    return e;
                }
                if (index >= tab.length) {
                    throw new NoSuchElementException();
                }
                E e = (E) tab[index];
                index = advance(index + 1);
                return e;
            }
        };
    }
}
