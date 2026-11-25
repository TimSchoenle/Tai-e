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

import org.jspecify.annotations.NonNull;
import pascal.taie.util.Hashes;

import java.io.Serializable;
import java.util.Collection;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.IntPredicate;

/**
 * Bit set based implementation of {@link java.util.Set}.
 * <p>
 * To store objects in bit set, the subclasses need to take care of
 * the mappings between objects and indexes by implementing {@link #getIndex}
 * and {@link #getElement}. The objects stored in the same bit set {@code s}
 * should preserve the invariant:
 * <code>e.equals(s.getElement(s.getIndex(e)))</code>.
 * <p>
 * Note: objects in different contexts may be mapped to the same index, and
 * it may cause unexpected behaviors if they are stored in the same bit set.
 * To avoid this, for each bit set, we require the subclasses to provide
 * a context object which indicates the context of the objects represented
 * by the bits in the set. We consider set operations (e.g., {@link #addAll}
 * and {@link #containsAll}) meaningful only when the two bit sets have
 * the equivalent context object.
 * <p>
 * TODO: add mod count
 *
 * @param <E> type of elements
 */
public abstract class GenericBitSet<E> extends AbstractSetEx<E>
        implements Serializable {

    protected IBitSet bitSet;

    protected GenericBitSet(boolean isSparse) {
        bitSet = IBitSet.newBitSet(isSparse);
    }

    @Override
    public boolean contains(Object o) {
        checkInvariant(o);
        return bitSet.get(getIndex((E) o));
    }

    @Override
    public boolean add(E e) {
        checkInvariant(e);
        return bitSet.set(getIndex(e));
    }

    @Override
    public boolean remove(Object o) {
        checkInvariant(o);
        return bitSet.clear(getIndex((E) o));
    }

    /**
     * The objects passed to this set should preserve this invariant.
     */
    private void checkInvariant(Object o) {
        assert o.equals(getElement(getIndex((E) o)));
    }

    @Override
    public boolean containsAll(@NonNull Collection<?> c) {
        if (c instanceof GenericBitSet s) {
            checkContext(s);
            return bitSet.contains(s.bitSet);
        } else {
            return super.containsAll(c);
        }
    }

    @Override
    public boolean addAll(@NonNull Collection<? extends E> c) {
        if (c instanceof GenericBitSet s) {
            checkContext(s);
            return bitSet.or(s.bitSet);
        } else {
            return super.addAll(c);
        }
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        if (c instanceof GenericBitSet s) {
            checkContext(s);
            return bitSet.andNot(s.bitSet);
        } else {
            return super.removeAll(c);
        }
    }

    @Override
    public boolean retainAll(@NonNull Collection<?> c) {
        if (c instanceof GenericBitSet s) {
            checkContext(s);
            return bitSet.and(s.bitSet);
        } else {
            return super.retainAll(c);
        }
    }

    /**
     * Sets the content of this bit set to the same as given collection.
     */
    public void setTo(@NonNull Collection<E> c) {
        if (c instanceof GenericBitSet s) {
            checkContext(s);
            bitSet.setTo(s.bitSet);
        } else {
            clear();
            addAll(c);
        }
    }

    /**
     * Checks if the set to operate on has equivalent context as this bit set.
     *
     * @param set the set to operate on
     */
    private void checkContext(GenericBitSet<?> set) {
        assert getContext().equals(set.getContext());
    }

    @Override
    public boolean isEmpty() {
        return bitSet.isEmpty();
    }

    @Override
    public void clear() {
        bitSet.clear();
    }

    @Override
    public int size() {
        return bitSet.cardinality();
    }

    @Override
    public Iterator<E> iterator() {
        return new BitSetIterator();
    }

    private class BitSetIterator implements Iterator<E> {

        /**
         * Current bit index of a set bit.
         */
        private int index;

        /**
         * Index of last iterated set bit; -1 if no such
         */
        private int lastRet;

        private BitSetIterator() {
            index = bitSet.nextSetBit(0);
            lastRet = -1;
        }

        @Override
        public boolean hasNext() {
            return index != -1;
        }

        @Override
        public E next() {
            int i = index;
            if (i == -1) {
                throw new NoSuchElementException();
            }
            index = bitSet.nextSetBit(i + 1); // advance
            return getElement(lastRet = i);
        }

        @Override
        public void remove() {
            if (lastRet < 0) {
                throw new IllegalStateException();
            }
            bitSet.clear(lastRet);
            lastRet = -1;
        }
    }

    @Override
    public int hashCode() {
        return hash(getContext(), bitSet.hashCode());
    }

    /**
     * @return the {@link #hashCode()} of a bit set of the given context
     * whose bits have the given hash code, as
     * {@link Hashes#hash(Object, Object)} without boxing.
     */
    private static int hash(Object context, int bitsHash) {
        return context.hashCode() * 31 + bitsHash;
    }

    /**
     * @return true if {@code other} has the same context and holds exactly
     * the same bits as this set.
     */
    public boolean sameBits(GenericBitSet<?> other) {
        return getContext() == other.getContext() && bitSet.equals(other.bitSet);
    }

    /**
     * @return true if this set and {@code other} have the same context and
     * both keep their bits in a {@link SparseBitSet}, so that
     * {@link #unionSummary} and {@link #addedBy} apply.
     */
    public boolean isSparseWith(GenericBitSet<?> other) {
        return getContext() == other.getContext()
                && bitSet instanceof SparseBitSet
                && other.bitSet instanceof SparseBitSet;
    }

    /**
     * Reads what {@code addAll(other)} would make of this set without
     * changing it; requires {@link #isSparseWith isSparseWith(other)}.
     *
     * @return the {@link #hashCode()} of the union in the low 32 bits and
     * its size in the high 32 bits, as {@link SparseBitSet#orSummary}
     */
    public long unionSummary(GenericBitSet<?> other) {
        long bits = ((SparseBitSet) bitSet).orSummary((SparseBitSet) other.bitSet);
        int hash = hash(getContext(), SparseBitSet.unionHash(bits));
        return (bits & 0xFFFFFFFF00000000L) | (hash & 0xFFFFFFFFL);
    }

    /**
     * @return true if this set keeps its bits in a {@link SparseBitSet}, so
     * that {@link #addSummary} applies.
     */
    public boolean isSparse() {
        return bitSet instanceof SparseBitSet;
    }

    /**
     * Reads what adding each of {@code elements} in turn would make of this
     * set without changing it; requires {@link #isSparse()}.
     *
     * @return the {@link #hashCode()} of the result in the low 32 bits and
     * its size in the high 32 bits, as {@link #unionSummary}
     */
    public long addSummary(Collection<? extends E> elements) {
        int[] indexes = new int[elements.size()];
        int i = 0;
        for (E e : elements) {
            indexes[i++] = getIndex(e);
        }
        long bits = ((SparseBitSet) bitSet).setSummary(indexes);
        int hash = hash(getContext(), SparseBitSet.unionHash(bits));
        return (bits & 0xFFFFFFFF00000000L) | (hash & 0xFFFFFFFFL);
    }

    /**
     * @return a new set of this context holding the elements that
     * {@code addAll(other)} would add to this set; requires
     * {@link #isSparseWith isSparseWith(other)}. Neither set changes.
     */
    public GenericBitSet<E> addedBy(GenericBitSet<?> other) {
        GenericBitSet<E> result = newSet();
        result.bitSet = ((SparseBitSet) other.bitSet).minus((SparseBitSet) bitSet);
        return result;
    }

    /**
     * @return a new set of this context holding the elements of this set
     * that are also in {@code other}, the set that {@link #copy()} and then
     * {@code retainAll(other)} on the copy make; requires
     * {@link #isSparseWith isSparseWith(other)}. Neither set changes.
     */
    public GenericBitSet<E> intersection(GenericBitSet<?> other) {
        GenericBitSet<E> result = newSet();
        result.bitSet = ((SparseBitSet) bitSet).intersection((SparseBitSet) other.bitSet);
        return result;
    }

    /**
     * @return the estimated bytes of the bits of this set in the packed form
     * of {@link SparseBitSet#toPacked()} (a 16-byte array header and eight
     * bytes a word), or of the words up to {@link IBitSet#length()} for a
     * bit set that is not sparse. A measurement that copies and allocates
     * nothing.
     */
    public long packedBytes() {
        long words = bitSet instanceof SparseBitSet sparse
                ? sparse.packedLength()
                : (bitSet.length() + (long) Long.SIZE - 1) / Long.SIZE;
        return 16L + 8L * words;
    }

    /**
     * Adds the storage shape of the bits of this set to {@code shape}: see
     * {@link SparseBitSet#addShape(long[])}; a bit set that is not sparse
     * adds its words up to {@link IBitSet#length()} as non-zero words, and
     * its set bits.
     *
     * @return whether the bits are a {@link SparseBitSet}
     */
    public boolean addShape(long[] shape) {
        if (bitSet instanceof SparseBitSet sparse) {
            sparse.addShape(shape);
            return true;
        }
        shape[SparseBitSet.SHAPE_WORDS] += (bitSet.length() + (long) Long.SIZE - 1) / Long.SIZE;
        shape[SparseBitSet.SHAPE_BITS] += bitSet.cardinality();
        return false;
    }

    @Override
    public SetEx<E> copy() {
        GenericBitSet<E> copy = newSet();
        copy.bitSet = bitSet.copy();
        return copy;
    }

    @Override
    public SetEx<E> addAllDiff(Collection<? extends E> c) {
        if (c instanceof GenericBitSet s) {
            checkContext(s);
            GenericBitSet<E> diff = newSet();
            diff.bitSet = bitSet.orDiff(s.bitSet);
            return diff;
        } else {
            return super.addAllDiff(c);
        }
    }

    /**
     * Brings a memo of a predicate up to date for the elements of this set,
     * and counts the elements of this set that the memo accepts: each
     * element of this set that is not in {@code known} is tested once, in
     * the iteration order of this set, and added to {@code known}, and also
     * to {@code pass} if the predicate accepts it. This set is not changed.
     * The predicate gets the index of the element (see {@link #getIndex}),
     * so no element is looked up unless the predicate does it.
     * See {@link IBitSet#updateMemoAndCount}.
     *
     * @param known the elements tested so far
     * @param pass  the tested elements that were accepted
     * @param test  the predicate on element indexes; it must not change any
     *              of the three sets
     * @return the number of elements of this set that are in {@code pass}
     * after the update
     */
    public int updateMemoAndCountByIndex(GenericBitSet<E> known, GenericBitSet<E> pass,
                                         IntPredicate test) {
        checkContext(known);
        checkContext(pass);
        return bitSet.updateMemoAndCount(known.bitSet, pass.bitSet, test);
    }

    /**
     * Performs the action on every element that is in both this set and
     * the given set, in the iteration order of this set. Neither set is
     * changed.
     *
     * @param other  a bit set of the same context
     * @param action the action; it must not change either set
     */
    public void forEachIntersection(GenericBitSet<E> other, Consumer<? super E> action) {
        checkContext(other);
        bitSet.forEachAnd(other.bitSet, i -> action.accept(getElement(i)));
    }

    @Override
    protected abstract GenericBitSet<E> newSet();

    @Override
    public boolean hasOverlapWith(Set<E> other) {
        if (other instanceof GenericBitSet s) {
            checkContext(s);
            return bitSet.intersects(s.bitSet);
        } else {
            return super.hasOverlapWith(other);
        }
    }

    /**
     * @return the context for the objects represented by the bits in this set.
     */
    protected abstract Object getContext();

    /**
     * Maps an object to the corresponding index.
     */
    protected abstract int getIndex(E o);

    /**
     * Maps an index to the corresponding object.
     */
    protected abstract E getElement(int index);
}
