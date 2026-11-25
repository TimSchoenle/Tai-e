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
import pascal.taie.util.collection.GenericBitSet;
import pascal.taie.util.collection.HybridBitSet;
import pascal.taie.util.collection.SetEx;
import pascal.taie.util.collection.SparseBitSet;

import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;

/**
 * The owners of the object sets on the heap, for splitting the bit set
 * blocks between them: the points-to sets of the pointers by their holder
 * count in the {@link PointsToSetInterner} (not shared, held by one, by
 * two, by more), the pending work list deltas (held as sets or as packed
 * words) and the exception sets of the method throw results.
 * <p>
 * Each row counts its entries (the references met) and, once per set
 * object by identity, the set: its objects, whether it is large and
 * whether it is stored packed, the blocks and non-zero words it stores
 * (see {@link SparseBitSet#addShape}), the estimated bytes of its word
 * storage ({@code block_bytes}: the level3 blocks of an unpacked sparse
 * set, all-zero ones included, else the one word array), eight bytes per
 * non-zero word ({@code word_bytes}) and the estimated bytes of the whole
 * set (the estimate of {@link PointsToSetCensus}). A set object met again
 * in a later row counts only as an entry there. A measurement: it reads
 * the sets and changes none.
 */
public final class HeapOwnerCensus {

    /**
     * Rows: points-to sets not in the interner (or without sharing).
     */
    public static final int UNSHARED = 0;

    /**
     * Rows: interned points-to sets held by one pointer (a set in the table
     * that no pointer holds counts here too).
     */
    public static final int HOLDERS_1 = 1;

    public static final int HOLDERS_2 = 2;

    /**
     * Rows: interned points-to sets held by three or more pointers.
     */
    public static final int HOLDERS_MANY = 3;

    public static final int PENDING_SET = 4;

    public static final int PENDING_PACKED = 5;

    public static final int THROW_RESULT = 6;

    public static final int ROWS = 7;

    private static final String[] ROW_NAMES = {
            "unshared", "holders_1", "holders_2", "holders_many",
            "pending_set", "pending_packed", "throw_result"};

    public static final int ENTRIES = 0;

    public static final int SETS = 1;

    public static final int OBJECTS = 2;

    public static final int LARGE = 3;

    public static final int PACKED = 4;

    public static final int BLOCKS = 5;

    public static final int WORDS = 6;

    public static final int BLOCK_BYTES = 7;

    public static final int WORD_BYTES = 8;

    public static final int BYTES = 9;

    public static final int COLUMNS = 10;

    private static final String[] COLUMN_NAMES = {
            "entries", "sets", "objects", "large", "packed", "blocks", "words",
            "block_bytes", "word_bytes", "bytes"};

    /**
     * The estimated bytes of a packed pending delta besides its words: the
     * array header.
     */
    private static final int ARRAY_HEADER = 16;

    private final long[][] figures = new long[ROWS][COLUMNS];

    private final Map<Object, Boolean> seen = new IdentityHashMap<>();

    private final long[] shape = new long[SparseBitSet.SHAPE_LENGTH];

    /**
     * Counts the points-to set held by one pointer in the row of its holder
     * count; a null set is not counted.
     */
    public void addPointer(@Nullable PointsToSet pts) {
        if (pts != null) {
            addPointsToSet(holderRow(pts), pts);
        }
    }

    /**
     * Counts a pending delta held as a set.
     */
    public void addPending(PointsToSet pts) {
        addPointsToSet(PENDING_SET, pts);
    }

    /**
     * Counts a pending delta held as the packed words of
     * {@link SparseBitSet#toPacked()}.
     */
    public void addPending(long[] packed) {
        long[] row = figures[PENDING_PACKED];
        ++row[ENTRIES];
        if (seen.put(packed, Boolean.TRUE) != null) {
            return;
        }
        long blocks = 0;
        long objects = 0;
        for (int at = 0; at < packed.length; ++blocks) {
            int words = Integer.bitCount((int) packed[at]);
            for (int w = at + 1; w <= at + words; ++w) {
                objects += Long.bitCount(packed[w]);
            }
            at += 1 + words;
        }
        long bytes = ARRAY_HEADER + 8L * packed.length;
        ++row[SETS];
        row[OBJECTS] += objects;
        ++row[LARGE];
        ++row[PACKED];
        row[BLOCKS] += blocks;
        row[WORDS] += packed.length - blocks;
        row[BLOCK_BYTES] += bytes;
        row[WORD_BYTES] += 8L * (packed.length - blocks);
        row[BYTES] += bytes;
    }

    /**
     * Counts one exception set of a method throw result.
     */
    public void addThrowSet(SetEx<?> set) {
        long[] row = figures[THROW_RESULT];
        ++row[ENTRIES];
        if (seen.put(set, Boolean.TRUE) != null) {
            return;
        }
        ++row[SETS];
        if (set instanceof GenericBitSet<?> bits) {
            ++row[LARGE];
            row[OBJECTS] += addBits(row, bits, false);
        } else {
            row[OBJECTS] += set.size();
        }
    }

    /**
     * @return the figure of a row ({@link #UNSHARED} to
     * {@link #THROW_RESULT}) and column ({@link #ENTRIES} to {@link #BYTES}).
     */
    public long get(int row, int column) {
        return figures[row][column];
    }

    /**
     * @return the sum of a column over the rows {@code [from, to)}.
     */
    public long sum(int from, int to, int column) {
        long sum = 0;
        for (int row = from; row < to; ++row) {
            sum += figures[row][column];
        }
        return sum;
    }

    /**
     * Drops the identity set of the sets seen, keeping the figures.
     */
    public void finish() {
        seen.clear();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("heap owners:");
        for (int row = 0; row < ROWS; ++row) {
            sb.append("\n  ").append(ROW_NAMES[row]);
            for (int column = 0; column < COLUMNS; ++column) {
                sb.append(' ').append(COLUMN_NAMES[column]).append('=')
                        .append(figures[row][column]);
            }
        }
        return sb.toString();
    }

    private static int holderRow(PointsToSet pts) {
        if (!(pts instanceof DelegatePointsToSet delegate) || delegate.holders < 0) {
            return UNSHARED;
        }
        return switch (delegate.holders) {
            case 0, 1 -> HOLDERS_1;
            case 2 -> HOLDERS_2;
            default -> HOLDERS_MANY;
        };
    }

    private void addPointsToSet(int rowIndex, PointsToSet pts) {
        long[] row = figures[rowIndex];
        ++row[ENTRIES];
        if (seen.put(pts, Boolean.TRUE) != null) {
            return;
        }
        ++row[SETS];
        long bytes = PointsToSetCensus.SET_OBJECTS;
        // the shape is read without size(): the size refreshes the state of
        // a sparse bit set, which drops its all-zero blocks
        if (pts instanceof DelegatePointsToSet delegate
                && delegate.set instanceof HybridBitSet<?> hybrid
                && hybrid.isLarge()
                && hybrid.set instanceof GenericBitSet<?> bits) {
            ++row[LARGE];
            row[BYTES] += bytes;
            row[OBJECTS] += addBits(row, bits, delegate.isPacked());
        } else {
            int n = pts.size();
            row[OBJECTS] += n;
            row[BYTES] += bytes + PointsToSetCensus.smallBytes(n);
        }
    }

    /**
     * @return the set bits of {@code bits}
     */
    private long addBits(long[] row, GenericBitSet<?> bits, boolean packed) {
        Arrays.fill(shape, 0);
        boolean sparse = bits.addShape(shape);
        if (packed) {
            ++row[PACKED];
        }
        row[BLOCKS] += shape[SparseBitSet.SHAPE_BLOCKS];
        row[WORDS] += shape[SparseBitSet.SHAPE_WORDS];
        row[BLOCK_BYTES] += PointsToSetCensus.blockBytes(shape, sparse, packed);
        row[WORD_BYTES] += 8L * shape[SparseBitSet.SHAPE_WORDS];
        row[BYTES] += PointsToSetCensus.bitSetBytes(shape, sparse, packed);
        return shape[SparseBitSet.SHAPE_BITS];
    }
}
