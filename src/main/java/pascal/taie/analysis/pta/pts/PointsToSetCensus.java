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

package pascal.taie.analysis.pta.pts;

import org.jspecify.annotations.Nullable;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.util.collection.HybridBitSet;
import pascal.taie.util.collection.HybridHashSet;
import pascal.taie.util.collection.SparseBitSet;

import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;

/**
 * Block census of points-to sets, for sizing a packed set form. A block is
 * a block of {@link #WORDS_PER_BLOCK} 64-bit words of the sparse bit set
 * (bits {@code [512 b, 512 b + 512)} for block {@code b}), keyed by the
 * object index. Two populations are counted: all pointers (one entry per
 * pointer, null and empty sets as cardinality 0) and the distinct set
 * objects among them (by identity: the interned sets when points-to sets
 * are shared, else one per pointer with a non-null set).
 * <p>
 * The byte figures are estimates for a 64-bit JVM with compressed oops
 * (12-byte headers, 4-byte references, 8-byte alignment), for the distinct
 * sets only: today's form (wrapper, hybrid set, and either the small form
 * or the sparse bit set with its level1 table, level2 areas and level3
 * blocks) against the packed form of {@link SparseBitSet#toPacked()} for
 * the large sets (wrapper holding one long array: a header per nonzero
 * block and its nonzero words); small sets keep today's form in the packed
 * estimate.
 */
public final class PointsToSetCensus {

    /**
     * Words per block of the sparse bit set (its level3 block).
     */
    public static final int WORDS_PER_BLOCK = SparseBitSet.WORDS_PER_BLOCK;

    /**
     * Number of log2 buckets: values up to {@link Long#MAX_VALUE}.
     */
    public static final int BUCKETS = Long.SIZE;

    private static final int BITS_PER_BLOCK = WORDS_PER_BLOCK * Long.SIZE;

    /**
     * Blocks per level2 area of the sparse bit set.
     */
    private static final int BLOCKS_PER_AREA = SparseBitSet.BLOCKS_PER_AREA;

    private static final int HEADER = 12;

    private static final int REF = 4;

    private static final int ARRAY_HEADER = 16;

    /**
     * DelegatePointsToSet: header, set reference, holders, intern hash.
     */
    private static final int WRAPPER = HEADER + REF + 4 + 4;

    /**
     * HybridBitSet: header, indexer, singleton and set references, two
     * booleans; rounded up.
     */
    private static final int HYBRID = 32;

    /**
     * IndexerBitSet (24), SparseBitSet (header, table reference, length,
     * state reference: 24) and its State object (four ints, two longs: 48).
     */
    private static final int SPARSE_OBJECTS = 24 + 24 + 48;

    /**
     * The small form: an ArraySet and its ArrayList.
     */
    private static final int SMALL_OBJECTS = 24 + 24;

    /**
     * The packed words reference and block count of a packed SparseBitSet.
     */
    private static final int PACKED_FIELDS = 8;

    /**
     * Capacity of the small form's array.
     */
    private static final int SMALL_CAPACITY = new HybridHashSet<>().getThreshold();

    /**
     * A bit set that is not sparse: its indexer wrapper (24) and the bit
     * set object (24), without the word array.
     */
    private static final int DENSE_OBJECTS = 24 + 24;

    /**
     * The objects of a points-to set before its elements: the wrapper and
     * the hybrid set.
     */
    static final int SET_OBJECTS = WRAPPER + HYBRID;

    /**
     * @return the estimated bytes of the small form of a set of {@code n}
     * objects (none for zero or one object, which the hybrid set holds
     * itself).
     */
    static long smallBytes(int n) {
        return n > 1 ? SMALL_OBJECTS + align(ARRAY_HEADER + REF * (long) SMALL_CAPACITY) : 0;
    }

    /**
     * @return the estimated bytes of the word storage alone of one bit set
     * whose shape (see {@link SparseBitSet#addShape}) is {@code shape}:
     * the level3 blocks of an unpacked sparse set, the packed words of a
     * packed one, or the word array of a bit set that is not sparse.
     */
    static long blockBytes(long[] shape, boolean sparse, boolean packed) {
        if (!sparse) {
            return align(ARRAY_HEADER + 8L * shape[SparseBitSet.SHAPE_WORDS]);
        }
        if (packed) {
            return align(ARRAY_HEADER + 8L * shape[SparseBitSet.SHAPE_PACKED_WORDS]);
        }
        return shape[SparseBitSet.SHAPE_BLOCKS] * align(ARRAY_HEADER + 8L * WORDS_PER_BLOCK);
    }

    /**
     * @return the estimated bytes of one bit set with its indexer wrapper
     * whose shape is {@code shape}: {@link #blockBytes} plus the objects,
     * and for an unpacked sparse set its level1 table and level2 areas.
     */
    static long bitSetBytes(long[] shape, boolean sparse, boolean packed) {
        long blocks = blockBytes(shape, sparse, packed);
        if (!sparse) {
            return DENSE_OBJECTS + blocks;
        }
        if (packed) {
            return SPARSE_OBJECTS + PACKED_FIELDS + blocks;
        }
        return SPARSE_OBJECTS + blocks
                + align(ARRAY_HEADER + REF * shape[SparseBitSet.SHAPE_TABLE])
                + shape[SparseBitSet.SHAPE_AREAS]
                * align(ARRAY_HEADER + REF * (long) BLOCKS_PER_AREA);
    }

    private final Population all = new Population();

    private final Population distinct = new Population();

    private final Map<PointsToSet, Boolean> seen = new IdentityHashMap<>();

    private long bytesToday;

    private long bytesPacked;

    private long largeDistinct;

    private long bytesTodayLarge;

    private long bytesPackedLarge;

    /**
     * Distinct large sets stored packed (see {@link DelegatePointsToSet#pack()}),
     * and the estimated bytes of all distinct large sets in the form they
     * are stored in.
     */
    private long largeStoredPacked;

    private long bytesStoredLarge;

    private int[] indexes = new int[16];

    /**
     * Counts the set held by one pointer.
     */
    public void add(@Nullable PointsToSet pts) {
        if (pts == null) {
            all.record(indexes, 0);
            return;
        }
        int n = collect(pts);
        all.record(indexes, n);
        if (seen.put(pts, Boolean.TRUE) == null) {
            Population.Shape shape = distinct.record(indexes, n);
            boolean large = pts instanceof DelegatePointsToSet d
                    && d.set instanceof HybridBitSet<?> && d.isLarge();
            long today = WRAPPER + HYBRID;
            long packed = today;
            if (large) {
                // the level1 table grows to the next power of two
                long tableLength = shape.areaSpan() <= 1 ? 1
                        : (long) Integer.highestOneBit(shape.areaSpan() - 1) << 1;
                today += SPARSE_OBJECTS + align(ARRAY_HEADER + REF * tableLength)
                        + shape.areas() * align(ARRAY_HEADER + REF * (long) BLOCKS_PER_AREA)
                        + shape.blocks() * align(ARRAY_HEADER + 8L * WORDS_PER_BLOCK);
                packed = WRAPPER + align(ARRAY_HEADER + 8L * shape.packedLength());
                largeDistinct++;
                bytesTodayLarge += today;
                bytesPackedLarge += packed;
                if (((DelegatePointsToSet) pts).isPacked()) {
                    largeStoredPacked++;
                    bytesStoredLarge += WRAPPER + HYBRID + SPARSE_OBJECTS + PACKED_FIELDS
                            + align(ARRAY_HEADER + 8L * shape.packedLength());
                } else {
                    bytesStoredLarge += today;
                }
            } else if (n > 1) {
                today += SMALL_OBJECTS + align(ARRAY_HEADER + REF * (long) SMALL_CAPACITY);
                packed = today;
            }
            bytesToday += today;
            bytesPacked += packed;
        }
    }

    /**
     * Drops the state that only {@link #add} needs (the identity set of
     * the sets seen), keeping the figures.
     */
    public void finish() {
        seen.clear();
        indexes = new int[0];
    }

    /**
     * Copies the sorted object indexes of the set into {@link #indexes}.
     *
     * @return the number of indexes.
     */
    private int collect(PointsToSet pts) {
        int n = 0;
        for (CSObj o : pts) {
            if (n == indexes.length) {
                indexes = Arrays.copyOf(indexes, n * 2);
            }
            indexes[n++] = o.getIndex();
        }
        Arrays.sort(indexes, 0, n);
        return n;
    }

    public Population all() {
        return all;
    }

    public Population distinct() {
        return distinct;
    }

    public long bytesToday() {
        return bytesToday;
    }

    public long bytesPacked() {
        return bytesPacked;
    }

    public long largeDistinct() {
        return largeDistinct;
    }

    public long bytesTodayLarge() {
        return bytesTodayLarge;
    }

    public long bytesPackedLarge() {
        return bytesPackedLarge;
    }

    public long largeStoredPacked() {
        return largeStoredPacked;
    }

    public long bytesStoredLarge() {
        return bytesStoredLarge;
    }

    @Override
    public String toString() {
        return "pts-census all: " + all + "\npts-census distinct: " + distinct
                + "\npts-census bytes (distinct, estimate): today=" + bytesToday
                + " packed=" + bytesPacked + " large-sets=" + largeDistinct
                + " large-today=" + bytesTodayLarge + " large-packed=" + bytesPackedLarge
                + " large-stored-packed=" + largeStoredPacked
                + " large-stored=" + bytesStoredLarge;
    }

    /**
     * @return the log2 bucket of a non-negative value: 0 for 0, else
     * {@code k} for a value in {@code [2^(k-1), 2^k)}.
     */
    public static int bucket(long value) {
        return Long.SIZE - Long.numberOfLeadingZeros(value);
    }

    /**
     * @return the non-empty buckets of a log2 histogram as
     * {@code [lo,hi]=count} entries.
     */
    public static String formatHistogram(long[] histogram) {
        StringBuilder sb = new StringBuilder("{");
        for (int k = 0; k < histogram.length; k++) {
            if (histogram[k] != 0) {
                if (sb.length() > 1) {
                    sb.append(", ");
                }
                long lo = k == 0 ? 0 : 1L << (k - 1);
                // 2^k - 1 without overflow at k = 63
                long hi = k == 0 ? 0 : (1L << (k - 1)) - 1 + (1L << (k - 1));
                sb.append('[').append(lo).append(',').append(hi).append("]=")
                        .append(histogram[k]);
            }
        }
        return sb.append('}').toString();
    }

    private static long align(long bytes) {
        return (bytes + 7) & ~7L;
    }

    private static int align(int bytes) {
        return (bytes + 7) & ~7;
    }

    /**
     * Histograms of one population of sets.
     */
    public static final class Population {

        /**
         * The block shape of one set.
         *
         * @param blocks   nonzero blocks
         * @param words    nonzero words
         * @param areas    level2 areas holding a nonzero block
         * @param areaSpan index of the last such area plus one (the
         *                 level1 table length it needs)
         */
        record Shape(int blocks, int words, int areas, int areaSpan) {

            /**
             * @return the length of {@link SparseBitSet#toPacked()} for
             * the set: a header per nonzero block plus its nonzero words.
             */
            long packedLength() {
                return (long) blocks + words;
            }
        }

        private long sets;

        private long objects;

        /**
         * Sets by cardinality, log2 buckets.
         */
        private final long[] cardinality = new long[BUCKETS];

        /**
         * Nonzero blocks by their count of nonzero words (index 1 to
         * {@link #WORDS_PER_BLOCK}).
         */
        private final long[] wordsPerBlock = new long[WORDS_PER_BLOCK + 1];

        /**
         * Sets by their count of nonzero blocks, log2 buckets.
         */
        private final long[] blocksPerSet = new long[BUCKETS];

        private long blocks;

        private long words;

        Shape record(int[] sorted, int n) {
            sets++;
            objects += n;
            cardinality[bucket(n)]++;
            int setBlocks = 0;
            int setWords = 0;
            int areas = 0;
            int lastArea = -1;
            int i = 0;
            while (i < n) {
                int block = sorted[i] / BITS_PER_BLOCK;
                int blockWords = 0;
                int lastWord = -1;
                while (i < n && sorted[i] / BITS_PER_BLOCK == block) {
                    int word = sorted[i] / Long.SIZE;
                    if (word != lastWord) {
                        blockWords++;
                        lastWord = word;
                    }
                    i++;
                }
                wordsPerBlock[blockWords]++;
                setBlocks++;
                setWords += blockWords;
                int area = block / BLOCKS_PER_AREA;
                if (area != lastArea) {
                    areas++;
                    lastArea = area;
                }
            }
            blocksPerSet[bucket(setBlocks)]++;
            blocks += setBlocks;
            words += setWords;
            return new Shape(setBlocks, setWords, areas, lastArea + 1);
        }

        public long sets() {
            return sets;
        }

        public long objects() {
            return objects;
        }

        public long blocks() {
            return blocks;
        }

        public long words() {
            return words;
        }

        public long[] cardinality() {
            return cardinality.clone();
        }

        public long[] wordsPerBlock() {
            return wordsPerBlock.clone();
        }

        public long[] blocksPerSet() {
            return blocksPerSet.clone();
        }

        @Override
        public String toString() {
            StringBuilder perBlock = new StringBuilder("{");
            for (int w = 1; w <= WORDS_PER_BLOCK; w++) {
                if (w > 1) {
                    perBlock.append(", ");
                }
                perBlock.append(w).append('=').append(wordsPerBlock[w]);
            }
            perBlock.append('}');
            return "sets=" + sets + " objects=" + objects + " blocks=" + blocks
                    + " words=" + words + " cardinality=" + formatHistogram(cardinality)
                    + " words-per-block=" + perBlock
                    + " blocks-per-set=" + formatHistogram(blocksPerSet);
        }
    }
}
