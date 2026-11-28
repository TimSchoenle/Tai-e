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
import org.jspecify.annotations.Nullable;
import pascal.taie.util.Indexer;

import java.io.Serializable;
import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

/**
 * Hybrid set that uses bit set for large set.
 * <p>
 * It is important to note that batch operations such as {@link #addAll(Collection)},
 * {@link #removeAll(Collection)}, {@link #retainAll(Collection)}, and {@link #containsAll(Collection)}
 * can experience performance degradation when used with {@link IndexerBitSet}.
 * <p>
 * For example, when removing elements of a {@link HybridBitSet} from an {@link IndexerBitSet}
 * (i.e., {@code indexerBitSet.removeAll(hybridBitSet)}) or vice versa,
 * the operation does not take advantage of bit-level operations.
 * Instead, it falls back on an iterative removal process that is less efficient.
 * <p>
 * Users are advised to be aware of these potential performance implications when performing
 * batch operations between {@link IndexerBitSet} and {@link HybridBitSet} instances
 * to avoid unexpected inefficiencies.
 *
 * @see IndexerBitSet
 */
public final class HybridBitSet<E> extends AbstractHybridSet<E>
        implements Serializable {

    private final Indexer<E> indexer;

    private final boolean isSparse;

    public HybridBitSet(Indexer<E> indexer, boolean isSparse) {
        this.indexer = indexer;
        this.isSparse = isSparse;
    }

    @Override
    protected Set<E> newLargeSet(int unused) {
        return new IndexerBitSet<>(indexer, isSparse);
    }

    @Override
    public boolean addAll(@NonNull Collection<? extends E> c) {
        // optimize when c is HybridBitSet
        if (this.set instanceof GenericBitSet<E> thisBitSet
                && c instanceof HybridBitSet<? extends E> other
                && other.set instanceof GenericBitSet<? extends E> otherBitSet) {
            return thisBitSet.addAll(otherBitSet);
        }
        return super.addAll(c);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        // optimize when c is HybridBitSet
        if (this.set instanceof GenericBitSet<E> thisBitSet
                && c instanceof HybridBitSet<?> other
                && other.set instanceof GenericBitSet<?> otherBitSet) {
            return thisBitSet.containsAll(otherBitSet);
        }
        return super.containsAll(c);
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        // optimize when c is HybridBitSet
        if (this.set instanceof GenericBitSet<E> thisBitSet
                && c instanceof HybridBitSet<?> other
                && other.set instanceof GenericBitSet<?> otherBitSet) {
            return thisBitSet.removeAll(otherBitSet);
        }
        return super.removeAll(c);
    }

    @Override
    public boolean retainAll(@NonNull Collection<?> c) {
        // optimize when c is HybridBitSet
        if (this.set instanceof GenericBitSet<E> thisBitSet
                && c instanceof HybridBitSet<?> other
                && other.set instanceof GenericBitSet<?> otherBitSet) {
            return thisBitSet.retainAll(otherBitSet);
        }
        return super.retainAll(c);
    }

    @Override
    public HybridBitSet<E> addAllDiff(Collection<? extends E> c) {
        HybridBitSet<E> diff = new HybridBitSet<>(indexer, isSparse);
        if (c instanceof HybridBitSet other && other.isLargeSet) {
            //noinspection unchecked
            SetEx<E> otherSet = (SetEx<E>) other.set;
            Set<E> diffSet;
            if (set == null) {
                set = otherSet.copy();
                diffSet = otherSet.copy();
                if (singleton != null) {
                    set.add(singleton);
                    diffSet.remove(singleton);
                    singleton = null;
                }
            } else if (!isLargeSet) {
                // current set is small set
                Set<E> oldSet = set;
                set = otherSet.copy();
                diffSet = otherSet.copy();
                set.addAll(oldSet);
                diffSet.removeAll(oldSet);
            } else {
                // current set is already a large set
                diffSet = ((SetEx<E>) set).addAllDiff(otherSet);
            }
            diff.set = diffSet;
            diff.isLargeSet = isLargeSet = true;
        } else {
            for (E e : c) {
                if (add(e)) {
                    diff.add(e);
                }
            }
        }
        return diff;
    }

    @Override
    public HybridBitSet<E> copy() {
        HybridBitSet<E> copy = new HybridBitSet<>(indexer, isSparse);
        copy.singleton = singleton;
        copy.isLargeSet = isLargeSet;
        if (set != null) {
            copy.set = ((SetEx<E>) set).copy();
        }
        return copy;
    }

    /**
     * Packs this set when it is a large sparse set of {@code expectedIndexer}:
     * the set itself is sparse and both it and its bits use that indexer,
     * the form {@link #ofPackedLarge} restores.
     *
     * @return the packed words of {@link SparseBitSet#toPacked()}, or
     * {@code null} when this set is small, dense or of another indexer
     */
    public long @Nullable [] toPackedLarge(Indexer<E> expectedIndexer) {
        SparseBitSet sparse = largeSparseBits(expectedIndexer);
        return sparse == null ? null : sparse.toPacked();
    }

    /**
     * {@link #toPackedLarge} without a copy for a set that is packed
     * already: a snapshot that shares its packed words.
     *
     * @return the snapshot of {@link SparseBitSet#packedSnapshot()}, or
     * {@code null} when {@link #toPackedLarge} returns {@code null} or the
     * sparse bit set of this set is not packed
     */
    public SparseBitSet.@Nullable PackedSnapshot packedLargeSnapshot(Indexer<E> expectedIndexer) {
        SparseBitSet sparse = largeSparseBits(expectedIndexer);
        return sparse == null ? null : sparse.packedSnapshot();
    }

    /**
     * Tells, without restoring them, whether the words of
     * {@link #toPackedLarge} of a set of {@code expectedIndexer} hold every
     * element of this set; the words are only read.
     *
     * @return {@code true} if they hold every element; {@code false} if
     * they do not, or if this set is large but not a large sparse set of
     * {@code expectedIndexer}, which this test does not read
     */
    public boolean isCoveredByPackedLarge(Indexer<E> expectedIndexer, long[] packed) {
        if (isLargeSet) {
            SparseBitSet sparse = largeSparseBits(expectedIndexer);
            return sparse != null && SparseBitSet.packedContains(packed, sparse);
        }
        return SparseBitSet.packedContains(packed, smallIndexes(expectedIndexer));
    }

    /**
     * {@link #isCoveredByPackedLarge(Indexer, long[])} for the snapshot of
     * {@link #packedLargeSnapshot} of a set of {@code expectedIndexer}; the
     * shared words are only read.
     */
    public boolean isCoveredByPackedLarge(Indexer<E> expectedIndexer,
                                          SparseBitSet.PackedSnapshot snapshot) {
        if (isLargeSet) {
            SparseBitSet sparse = largeSparseBits(expectedIndexer);
            return sparse != null && SparseBitSet.packedContains(snapshot, sparse);
        }
        return SparseBitSet.packedContains(snapshot, smallIndexes(expectedIndexer));
    }

    /**
     * @return the indexes of the elements of this small set by
     * {@code indexer}
     */
    private int[] smallIndexes(Indexer<E> indexer) {
        int[] indexes = new int[size()];
        int i = 0;
        for (E e : this) {
            indexes[i++] = indexer.getIndex(e);
        }
        return indexes;
    }

    /**
     * @return the sparse bit set of this set when it is a large sparse set
     * of {@code expectedIndexer} (see {@link #toPackedLarge}), else
     * {@code null}
     */
    private @Nullable SparseBitSet largeSparseBits(Indexer<E> expectedIndexer) {
        if (isLargeSet && isSparse && indexer == expectedIndexer
                && set instanceof IndexerBitSet<E> bits
                && bits.getContext() == expectedIndexer
                && bits.bitSet instanceof SparseBitSet sparse) {
            return sparse;
        }
        return null;
    }

    /**
     * Packs the sparse bit set of this set if it is large (see
     * {@link SparseBitSet#pack()}); the contents do not change.
     */
    public void packLarge() {
        if (isLargeSet && set instanceof GenericBitSet<E> bits
                && bits.bitSet instanceof SparseBitSet sparse) {
            sparse.pack();
        }
    }

    /**
     * @return {@code true} if this set is large and its sparse bit set is
     * packed.
     */
    public boolean isPackedLarge() {
        return isLargeSet && set instanceof GenericBitSet<E> bits
                && bits.bitSet instanceof SparseBitSet sparse && sparse.isPacked();
    }

    /**
     * Restores a large sparse set from the words of {@link #toPackedLarge}:
     * the result equals the packed set as a {@link #copy()} of it would,
     * large set flag included.
     */
    public static <E> HybridBitSet<E> ofPackedLarge(Indexer<E> indexer, long[] packed) {
        return ofLargeSparse(indexer, SparseBitSet.ofPacked(packed));
    }

    /**
     * Restores a large sparse set from the snapshot of
     * {@link #packedLargeSnapshot}: the result equals what
     * {@link #ofPackedLarge(Indexer, long[])} makes of the words of
     * {@link #toPackedLarge} of the snapshotted set.
     */
    public static <E> HybridBitSet<E> ofPackedLarge(
            Indexer<E> indexer, SparseBitSet.PackedSnapshot snapshot) {
        return ofLargeSparse(indexer, SparseBitSet.ofSnapshot(snapshot));
    }

    private static <E> HybridBitSet<E> ofLargeSparse(Indexer<E> indexer, SparseBitSet sparse) {
        HybridBitSet<E> result = new HybridBitSet<>(indexer, true);
        IndexerBitSet<E> bits = new IndexerBitSet<>(indexer, true);
        bits.bitSet = sparse;
        result.set = bits;
        result.isLargeSet = true;
        return result;
    }

    /**
     * @return true if {@link #addAllDiff(Collection) addAllDiff(c)} would
     * leave this set unchanged in its form and elements.
     */
    public boolean addAllDiffKeeps(HybridBitSet<? extends E> c) {
        if (c.isLargeSet) {
            // a large c turns this set large (see addAllDiff)
            return isLargeSet && containsAll(c);
        }
        if (c.isEmpty()) {
            return true;
        }
        if (!isLargeSet && set != null && set.size() + 1 > getThreshold()) {
            // add upgrades a full small set before it looks for the element
            return false;
        }
        return containsAll(c);
    }

    /**
     * @return true if this set is in the large form with its bits in a
     * sparse bit set, and {@code c} is a set of the same indexer that is
     * either in the large form with its bits in a sparse bit set of the same
     * context, or a singleton or small set: the case in which
     * {@link #unionSummary}, {@link #isUnionOf} and {@link #unionDiff} read
     * {@link #addAllDiff addAllDiff(c)} without changing this set.
     */
    public boolean canSummarizeUnion(HybridBitSet<?> c) {
        if (form() != FORM_LARGE || indexer != c.indexer
                || !(set instanceof GenericBitSet<E> bits)) {
            return false;
        }
        int cForm = c.form();
        if (cForm == FORM_LARGE) {
            return c.set instanceof GenericBitSet<?> other && bits.isSparseWith(other);
        }
        // addAllDiff takes the branch of a small c by its large set flag
        return !c.isLargeSet && cForm != FORM_EMPTY && bits.isSparse();
    }

    /**
     * Reads the set that {@link #addAllDiff addAllDiff(c)} would make of
     * this set, without changing it: from the state of this set and one
     * pass over the words of a large {@code c}, or over the elements of a
     * small one; requires {@link #canSummarizeUnion canSummarizeUnion(c)}.
     *
     * @return the {@link #sequenceHash()} of that set and its size, in the
     * format of {@link SparseBitSet#orSummary}
     */
    public long unionSummary(HybridBitSet<?> c) {
        GenericBitSet<E> bits = (GenericBitSet<E>) set;
        long summary = c.isLargeSet
                ? bits.unionSummary((GenericBitSet<?>) c.set)
                : bits.addSummary((HybridBitSet<? extends E>) c);
        int hash = largeSequenceHash(SparseBitSet.unionHash(summary));
        return (summary & 0xFFFFFFFF00000000L) | (hash & 0xFFFFFFFFL);
    }

    /**
     * @return true if this set is the same by {@link #sameSequence} as the
     * set that {@code a.addAllDiff(b)} would make of {@code a}, where
     * {@code summary} is {@code a.unionSummary(b)}; requires
     * {@code a.canSummarizeUnion(b)}.
     */
    public boolean isUnionOf(HybridBitSet<?> a, HybridBitSet<?> b, long summary) {
        // a superset of both of the size of the union is the union
        return form() == FORM_LARGE && indexer == a.indexer
                && set instanceof GenericBitSet<E> bits
                && bits.isSparseWith((GenericBitSet<?>) a.set)
                && bits.size() == SparseBitSet.unionCardinality(summary)
                && bits.containsAll(a.set)
                && (b.isLargeSet ? bits.containsAll(b.set) : bits.containsAll(b));
    }

    /**
     * @return the difference that {@link #addAllDiff addAllDiff(c)} would
     * return, with the same form and elements, without changing this set;
     * requires {@link #canSummarizeUnion canSummarizeUnion(c)}.
     */
    public HybridBitSet<E> unionDiff(HybridBitSet<? extends E> c) {
        HybridBitSet<E> diff = new HybridBitSet<>(indexer, isSparse);
        if (c.isLargeSet) {
            diff.set = ((GenericBitSet<E>) set).addedBy((GenericBitSet<?>) c.set);
            diff.isLargeSet = true;
        } else {
            // addAllDiff adds each element of a small c that this large set
            // lacks to the difference, in the iteration order of c
            for (E e : c) {
                if (!set.contains(e)) {
                    diff.add(e);
                }
            }
        }
        return diff;
    }

    /**
     * @return true if this set is large and held in a bit set that is
     * {@link GenericBitSet#isSparseWith sparse with} {@code bits}, so that
     * {@link #largeIntersection} applies.
     */
    public boolean canIntersectLarge(GenericBitSet<?> bits) {
        return isLargeSet && set instanceof GenericBitSet<E> own && own.isSparseWith(bits);
    }

    /**
     * @return a new set of the elements of this set that are also in
     * {@code bits}, in the form that {@link #copy()} and then
     * {@code retainAll(bits)} on the bit set of the copy give it; requires
     * {@link #canIntersectLarge canIntersectLarge(bits)}. This set does not
     * change.
     */
    public HybridBitSet<E> largeIntersection(GenericBitSet<?> bits) {
        HybridBitSet<E> result = new HybridBitSet<>(indexer, isSparse);
        result.set = ((GenericBitSet<E>) set).intersection(bits);
        result.isLargeSet = isLargeSet;
        return result;
    }

    /**
     * @return true if this set is in its large (bit set) form.
     */
    public boolean isLarge() {
        return isLargeSet;
    }

    /**
     * Hash of {@link #sameSequence(HybridBitSet)}: of the form of this set
     * and of its elements in iteration order.
     */
    public int sequenceHash() {
        int form = form();
        int hash = form;
        if (form == FORM_SINGLETON) {
            hash = 31 * hash + indexer.getIndex(singleton);
        } else if (form == FORM_SMALL) {
            for (E e : set) {
                hash = 31 * hash + indexer.getIndex(e);
            }
        } else if (form == FORM_LARGE) {
            hash = largeSequenceHash(set.hashCode());
        }
        return hash;
    }

    /**
     * @return the {@link #sequenceHash()} of a large set whose bit set has
     * the given hash code.
     */
    private static int largeSequenceHash(int setHash) {
        return 31 * FORM_LARGE + setHash;
    }

    /**
     * Compares the form (empty, singleton, small or large) and the elements
     * in iteration order. Two sets that are the same by this comparison
     * iterate in the same order and stay so under the same operations.
     */
    public boolean sameSequence(HybridBitSet<?> other) {
        int form = form();
        if (form != other.form() || indexer != other.indexer) {
            return false;
        }
        return switch (form) {
            case FORM_SINGLETON -> singleton.equals(other.singleton);
            case FORM_SMALL -> sameOrder(set, other.set);
            case FORM_LARGE -> ((GenericBitSet<E>) set).sameBits((GenericBitSet<?>) other.set);
            default -> true;
        };
    }

    private static final int FORM_EMPTY = 0;

    private static final int FORM_SINGLETON = 1;

    private static final int FORM_SMALL = 2;

    private static final int FORM_LARGE = 3;

    private int form() {
        if (singleton != null) {
            return FORM_SINGLETON;
        } else if (set == null) {
            return FORM_EMPTY;
        } else {
            return isLargeSet ? FORM_LARGE : FORM_SMALL;
        }
    }

    private static boolean sameOrder(Set<?> a, Set<?> b) {
        if (a.size() != b.size()) {
            return false;
        }
        Iterator<?> ia = a.iterator();
        Iterator<?> ib = b.iterator();
        while (ia.hasNext()) {
            if (!ia.next().equals(ib.next())) {
                return false;
            }
        }
        return true;
    }
}
