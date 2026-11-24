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

import org.jspecify.annotations.Nullable;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serial;
import java.io.Serializable;
import java.util.function.IntConsumer;
import java.util.function.IntPredicate;

/**
 * Sparse bit set. This implementation groups bits into blocks, and it could
 * avoid allocating words to represent continuous zero bits when possible.
 * This design saves memory and improves efficiency of set iterations.
 * <p>
 * This implementation uses core design and some code from
 * https://github.com/brettwooldridge/SparseBitSet
 * We rewrite most code to support the operations that we need
 * and improve the readability.
 */
public class SparseBitSet extends AbstractBitSet
        implements Serializable {

    // TODO: unify level1/2/3 and table/area/block
    // Currently:
    // w1/level1 = table
    // w2/level2 = area
    // w3/level3 = block

    //==============================================================================
    //  The critical parameters. These are set up so that the compiler may
    //  pre-compute all the values as compile-time constants.
    //==============================================================================

    /**
     * The number of bits in a positive integer, and the size of permitted index
     * of a bit in the bit set.
     */
    private static final int INDEX_SIZE = Integer.SIZE - 1;

    /**
     * LEVEL3 is the number of bits of the level3 address: a block holds
     * 2^LEVEL3 words (8 words, 512 bits). Small blocks keep sets small when
     * many blocks hold only a few bits; the price is a larger area array, so a
     * set with a single block in an area costs more than with large blocks.
     */
    private static final int LEVEL3 = 3;

    /**
     * LEVEL2 is the number of bits of the level2 address: an area holds
     * 2^LEVEL2 blocks. LEVEL2 + LEVEL3 fixes the span of one area (1024 words)
     * and with it the size of the level1 table.
     */
    private static final int LEVEL2 = 7;

    /**
     * LEVEL1 is the number of bits of the level1 address.
     */
    private static final int LEVEL1 = INDEX_SIZE - LEVEL2 - LEVEL3 - ADDRESS_BITS_PER_WORD;

    /**
     * MAX_LENGTH1 is the maximum number of entries in the level1 set array.
     */
    private static final int MAX_LENGTH1 = 1 << LEVEL1;

    /**
     * LENGTH2 is the number of entries in the any level2 area.
     */
    private static final int LENGTH2 = 1 << LEVEL2;

    /**
     * LENGTH3 is the number of entries in the any level3 block.
     */
    private static final int LENGTH3 = 1 << LEVEL3;

    /**
     * The shift to create the word index. (I.e., move it to the right end)
     */
    static final int SHIFT3 = ADDRESS_BITS_PER_WORD;

    /**
     * MASK3 is the mask to extract the LEVEL3 address from a word index
     * (after shifting by SHIFT3).
     */
    private static final int MASK3 = LENGTH3 - 1;

    /**
     * SHIFT2 is the shift to bring the level2 address (from the word index) to
     * the right end (i.e., after shifting by SHIFT3).
     */
    static final int SHIFT2 = LEVEL3;

    /**
     * MASK2 is the mask to extract the LEVEL2 address from a word index
     * (after shifting by SHIFT3 and SHIFT2).
     */
    private static final int MASK2 = LENGTH2 - 1;

    /**
     * SHIFT1 is the shift to bring the level1 address (from the word index) to
     * the right end (i.e., after shifting by SHIFT3).
     */
    static final int SHIFT1 = LEVEL2 + LEVEL3;

    /**
     * UNIT is the greatest number of bits that can be held in one level1 entry.
     * That is, bits per word by words per level3 block by blocks per level2 area.
     */
    private static final int UNIT = LENGTH2 * LENGTH3 * BITS_PER_WORD;

    /**
     * BITS_PER_WORD_SIZE is maximum index of a bit in a ADDRESS_BITS_PER_WORD word.
     */
    private static final int WORD_SIZE = BITS_PER_WORD - 1;

    /**
     * LENGTH3_SIZE is maximum index of a LEVEL3 page.
     */
    private static final int LENGTH3_SIZE = LENGTH3 - 1;

    /**
     * LENGTH2_SIZE is maximum index of a LEVEL2 page.
     */
    private static final int LENGTH2_SIZE = LENGTH2 - 1;

    // ------------------------------------------------------------------------
    // instance fields
    // ------------------------------------------------------------------------
    /**
     * The storage for this SparseBitSet. The <i>i</i>th bit is stored in a word
     * represented by a long value, and is at bit position <code>i % 64</code>
     * within that word (where bit position 0 refers to the least significant bit
     * and 63 refers to the most significant bit).
     * <p>
     * The words are organized into blocks, and the blocks are accessed by two
     * additional levels of array indexing.
     */
    private transient long[][][] table;

    /**
     * For the current size of the bits array, this is the maximum possible
     * length of the bit set, i.e., the index of the last possible bit, plus one.
     * Note: this not the value returned by <i>length</i>().
     *
     * @see #resize(int)
     * @see #length()
     */
    private transient int bitsLength;

    private transient State state;

    public SparseBitSet() {
        this(1);
    }

    public SparseBitSet(int nbits) {
        if (nbits < 0) {
            throw new NegativeArraySizeException("nbits < 0: " + nbits);
        }
        resize(nbits - 1);
        state = new State();
        updateState();
    }

    @Override
    public boolean set(int bitIndex) {
        if ((bitIndex + 1) < 1) {
            throw new IndexOutOfBoundsException("bitIndex=" + bitIndex);
        }
        if (bitIndex >= bitsLength) {
            resize(bitIndex);
        }

        final int w = wordIndex(bitIndex);
        final int w1 = level1Index(w);
        final int w2 = level2Index(w);
        long[] a3 = getBlock(table, w1, w2);
        if (a3 == null) {
            a3 = getOrCreateBlock(w1, w2);
            // the block receives the bit below, so it does not stay all zero
            recordNewBlock();
        }
        int w3 = level3Index(w);
        long oldWord = a3[w3];
        long newWord = oldWord | (1L << bitIndex);
        if (oldWord != newWord) {
            a3[w3] = newWord;
            recordWord(w, oldWord, newWord);
            return true;
        }
        return false;
    }

    @Override
    public boolean clear(int bitIndex) {
        if ((bitIndex + 1) < 1) {
            throw new IndexOutOfBoundsException("bitIndex=" + bitIndex);
        }
        if (bitIndex >= bitsLength) {
            return false;
        }
        final int w = wordIndex(bitIndex);
        long[][] a2;
        if ((a2 = table[level1Index(w)]) == null) {
            return false;
        }
        long[] a3;
        if ((a3 = a2[level2Index(w)]) == null) {
            return false;
        }
        int w3 = level3Index(w);
        long oldWord = a3[w3];
        long newWord = oldWord & ~(1L << bitIndex); //  Clear the indicated bit
        if (oldWord != newWord) {
            // In the interests of speed, no check is made here on whether the
            // level3 block goes to all zero. This may be found and corrected
            // in some later operation.
            a3[w3] = newWord;
            invalidateState();
            return true;
        }
        return false;
    }

    @Override
    public boolean get(int bitIndex) {
        if ((bitIndex + 1) < 1) {
            throw new IndexOutOfBoundsException("bitIndex=" + bitIndex);
        }
        final int w = wordIndex(bitIndex);
        long[][] a2;
        long[] a3;
        return bitIndex < bitsLength
                && (a2 = table[level1Index(w)]) != null
                && (a3 = a2[level2Index(w)]) != null
                && ((a3[level3Index(w)] & (1L << bitIndex)) != 0);
    }

    @Override
    public void flip(int bitIndex) {
        if ((bitIndex + 1) < 1) {
            throw new IndexOutOfBoundsException("bitIndex=" + bitIndex);
        }
        if (bitIndex >= bitsLength) {
            resize(bitIndex);
        }
        final int w = wordIndex(bitIndex);
        final int w1 = level1Index(w);
        final int w2 = level2Index(w);
        long[] a3 = getOrCreateBlock(w1, w2);
        a3[level3Index(w)] ^= (1L << bitIndex); // Flip the designated bit
        invalidateState();
    }

    @Override
    public int nextSetBit(int fromIndex) {
        // The index value of this method is permitted to be Integer.MAX_VALUE,
        // as this is needed to make the loop defined above work: just in case the
        // bit labelled Integer.MAX_VALUE-1 is set. This case is not optimised:
        // but eventually -1 will be returned, as this will be included with
        // any search that goes off the end of the level1 array.
        if (fromIndex < 0) {
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        }
        // This is the word from which the search begins.
        int w = wordIndex(fromIndex);
        int w1 = level1Index(w);
        int w2 = level2Index(w);
        int w3 = level3Index(w);

        long word = 0L;
        final int tableLength = table.length;

        long[][] a2;
        long[] a3;
        // first check whether bitIndex itself (or the bits next to bitIndex
        // in the same word) has been set
        if (w1 < tableLength && ((a2 = table[w1]) == null
                || (a3 = a2[w2]) == null
                || ((word = a3[w3] & (~0L << fromIndex)) == 0L))) {
            // bitIndex is not set, start a search since bitIndex + 1
            ++w;
            w1 = level1Index(w);
            w2 = level2Index(w);
            w3 = level3Index(w);
            outer:
            for (; w1 != tableLength; ++w1) {
                if ((a2 = table[w1]) != null) {
                    for (; w2 != LENGTH2; ++w2) {
                        if ((a3 = a2[w2]) != null) {
                            for (; w3 != LENGTH3; ++w3) {
                                if ((word = a3[w3]) != 0) {
                                    break outer;
                                }
                            }
                        }
                        w3 = 0; // reset w3
                    }
                }
                w2 = w3 = 0; // reset w2 and w3
            }
        }
        return (w1 >= tableLength ? -1
                : bitIndex(w1, w2, w3) + Long.numberOfTrailingZeros(word));
    }

    @Override
    public int nextClearBit(int fromIndex) {
        // The index of this method is permitted to be Integer.MAX_VALUE,
        // as this is needed to make this method work together with the method
        // nextSetBit()--as might happen if a search for the next clear bit is
        // started after finding a set bit labelled Integer.MAX_VALUE-1. This
        // case is not optimised, the code will eventually return -1 (since
        // the Integer.MAX_VALUE-th bit does "exist," and is 0).

        if (fromIndex < 0) {
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        }
        // This is the word from which the search begins.
        int w = wordIndex(fromIndex);
        int w1 = level1Index(w);
        int w2 = level2Index(w);
        int w3 = level3Index(w);

        long nword = (~0L << fromIndex);
        final int tableLength = table.length;

        long[][] a2;
        long[] a3;
        // first check whether bitIndex itself (or the bits next to bitIndex
        // in the same word) is clear (not set).
        if (w1 < tableLength && (a2 = table[w1]) != null
                && (a3 = a2[w2]) != null
                && ((nword = ~a3[w3] & (~0L << fromIndex))) == 0L) {
            // bitIndex is clear (not set), start a search since bitIndex + 1
            ++w;
            w1 = level1Index(w);
            w2 = level2Index(w);
            w3 = level3Index(w);
            nword = ~0L;
            outer:
            for (; w1 != tableLength; ++w1) {
                if ((a2 = table[w1]) == null) {
                    break;
                }
                for (; w2 != LENGTH2; ++w2) {
                    if ((a3 = a2[w2]) == null) {
                        break outer;
                    }
                    for (; w3 != LENGTH3; ++w3) {
                        if ((nword = ~a3[w3]) != 0) {
                            break outer;
                        }
                    }
                    w3 = 0;
                }
                w2 = w3 = 0;
            }
        }
        final int result = bitIndex(w1, w2, w3) + Long.numberOfTrailingZeros(nword);
        return (result == Integer.MAX_VALUE ? -1 : result);
    }

    @Override
    public int previousSetBit(int fromIndex) {
        if (fromIndex < 0) {
            if (fromIndex == -1) {
                return -1;
            }
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        }

        final long[][][] table = this.table;
        final int tableSize = table.length - 1;

        /*  This is the word from which the search begins. */
        final int w = wordIndex(fromIndex);
        int w1 = level1Index(w);
        int w2, w3, w4;
        if (w1 > tableSize) {
            // If the fromIndex is out of scope of table, then start from
            // the very end of the table.
            w1 = tableSize;
            w2 = LENGTH2_SIZE;
            w3 = LENGTH3_SIZE;
            w4 = WORD_SIZE;
        } else {
            w2 = level2Index(w);
            w3 = level3Index(w);
            w4 = fromIndex % BITS_PER_WORD;
        }
        long word;
        long[][] a2;
        long[] a3;
        for (; w1 >= 0; --w1) {
            if ((a2 = table[w1]) != null) {
                for (; w2 >= 0; --w2) {
                    if ((a3 = a2[w2]) != null) {
                        for (; w3 >= 0; --w3) {
                            if ((word = a3[w3]) != 0) {
                                for (int offset = w4; offset >= 0; --offset) {
                                    if ((word & (1L << offset)) != 0) {
                                        return bitIndex(w1, w2, w3) + offset;
                                    }
                                }
                            }
                            w4 = WORD_SIZE;
                        }
                    }
                    w3 = LENGTH3_SIZE;
                    w4 = WORD_SIZE;
                }
            }
            w2 = LENGTH2_SIZE;
            w3 = LENGTH3_SIZE;
            w4 = WORD_SIZE;
        }
        return -1;
    }

    @Override
    public int previousClearBit(int fromIndex) {
        if (fromIndex < 0) {
            if (fromIndex == -1) {
                return -1;
            }
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        }

        final long[][][] table = this.table;
        final int tableSize = table.length - 1;

        int w = wordIndex(fromIndex);
        int w1 = level1Index(w);
        if (w1 > tableSize) {
            return fromIndex;
        }
        int w2 = level2Index(w);
        int w3 = level3Index(w);
        int w4 = fromIndex % BITS_PER_WORD;

        long word;
        long[][] a2;
        long[] a3;

        for (; w1 >= 0; --w1) {
            if ((a2 = table[w1]) == null) {
                return bitIndex(w1, w2, w3) + w4;
            }
            for (; w2 >= 0; --w2) {
                if ((a3 = a2[w2]) == null) {
                    return bitIndex(w1, w2, w3) + w4;
                }
                for (; w3 >= 0; --w3) {
                    if ((word = a3[w3]) == 0) {
                        return bitIndex(w1, w2, w3) + w4;
                    }
                    for (int offset = w4; offset >= 0; --offset) {
                        if ((word & (1L << offset)) == 0) {
                            return bitIndex(w1, w2, w3) + offset;
                        }
                    }
                    w4 = WORD_SIZE;
                }
                w3 = LENGTH3_SIZE;
            }
            w2 = LENGTH2_SIZE;
        }
        return -1;
    }

    @Override
    public boolean intersects(IBitSet set) {
        if (this.isEmpty() || set.isEmpty()) {
            return false;
        }
        if (this == set) {
            return true;
        }
        if (!(set instanceof SparseBitSet other)) {
            return super.intersects(set);
        }
        return iterateBlocks(this, other, new IntersectsAction(this));
    }

    private static class IntersectsAction extends BlockAction<Boolean> {

        private boolean intersects = false;

        private IntersectsAction(SparseBitSet self) {
            super(self);
        }

        @Override
        boolean accept(int w1, int w2, long[] selfBlock, long[] iteratedBlock) {
            boolean isZero = true;
            if (selfBlock != null) {
                for (int w3 = 0; w3 < LENGTH3; ++w3) {
                    long selfWord = selfBlock[w3];
                    if (selfWord != 0) {
                        long iteratedWord = iteratedBlock[w3];
                        if ((selfWord & iteratedWord) != 0) {
                            intersects = true;
                            return false;
                        }
                        isZero = false;
                    }
                }
            }
            return isZero;
        }

        @Override
        boolean canBreak() {
            // already found intersection, can break the iteration.
            return intersects;
        }

        @Override
        Boolean getResult() {
            return intersects;
        }
    }

    @Override
    public boolean contains(IBitSet set) {
        if (this == set) {
            return true;
        }
        if (!(set instanceof SparseBitSet other)) {
            return super.contains(set);
        }
        return iterateBlocks(this, other, new ContainsAction(this));
    }

    private static class ContainsAction extends BlockAction<Boolean> {

        private boolean contains = true;

        private ContainsAction(SparseBitSet self) {
            super(self);
        }

        @Override
        boolean accept(int w1, int w2, long[] selfBlock, long[] iteratedBlock) {
            boolean isZero = true;
            if (selfBlock != null) {
                for (int w3 = 0; w3 < LENGTH3; ++w3) {
                    long selfWord = selfBlock[w3];
                    if (selfWord != 0) {
                        isZero = false;
                    }
                    long iteratedWord = iteratedBlock[w3];
                    if ((selfWord | iteratedWord) != selfWord) {
                        contains = false;
                    }
                }
            } else {
                contains = !isNonZeroBlock(iteratedBlock);
            }
            return isZero;
        }

        @Override
        boolean canBreak() {
            // already found not-contain bits, can break the iteration
            return !contains;
        }

        @Override
        Boolean getResult() {
            return contains;
        }
    }

    /**
     * Performs a logical <b>AND</b> of this target bit set with the
     * argument bit set. This operation cannot skip zero blocks in the
     * other set, thus we cannot implement it via {@link #iterateBlocks}.
     *
     * @param set a bit set
     * @return {@code true} if this bit set changed as a result of the call
     */
    @Override
    public boolean and(IBitSet set) {
        if (this == set) {
            return false;
        }
        if (!(set instanceof SparseBitSet other)) {
            throw new UnsupportedOperationException(
                    String.format("%s does not support AND with %s",
                            this.getClass(), set.getClass()));
        }
        // Unlike other set operations, AND requires iteration on
        // non-null blocks of both this and other sets.
        boolean changed = false;
        long[][][] thisTable = this.table;
        long[][][] otherTable = other.table;
        int w1InCommon = Math.min(thisTable.length, otherTable.length);
        // process common part
        for (int w1 = 0; w1 < w1InCommon; ++w1) {
            long[][] otherArea = otherTable[w1];
            long[][] thisArea = thisTable[w1];
            if (otherArea != null) {
                if (thisArea != null) {
                    // both areas are present
                    boolean isZeroArea = true;
                    for (int w2 = 0; w2 < LENGTH2; ++w2) {
                        long[] thisBlock = thisArea[w2];
                        long[] otherBlock = otherArea[w2];
                        if (otherBlock != null) {
                            if (thisBlock != null) {
                                // both blocks are present
                                boolean isZeroBlock = true;
                                // perform AND on each words
                                for (int w3 = 0; w3 < LENGTH3; ++w3) {
                                    long oldWord = thisBlock[w3];
                                    long newWord = oldWord & otherBlock[w3];
                                    if (oldWord != newWord) {
                                        thisBlock[w3] = newWord;
                                        changed = true;
                                    }
                                    if (newWord != 0) {
                                        isZeroBlock = false;
                                    }
                                }
                                if (isZeroBlock) {
                                    thisArea[w2] = null;
                                } else {
                                    isZeroArea = false;
                                }
                            }
                        } else if (isNonZeroBlock(thisBlock)) {
                            // otherBlock is null and thisBlock is not zero,
                            // then clear thisBlock and mark changed
                            thisArea[w2] = null;
                            changed = true;
                        }
                    }
                    if (isZeroArea) {
                        // iterate all thisBlocks and found they are all zero,
                        // then clear thisArea
                        thisTable[w1] = null;
                    }
                }
            } else if (isNonZeroArea(thisArea)) {
                // otherArea is null and thisArea is not zero,
                // then clear thisArea and mark changed
                thisTable[w1] = null;
                changed = true;
            }
        }
        // process extra part of this table
        if (w1InCommon < thisTable.length) {
            if (!changed) { // check whether extra areas are zero
                for (int w1 = w1InCommon; w1 < thisTable.length; ++w1) {
                    if (isNonZeroArea(thisTable[w1])) {
                        changed = true;
                        break;
                    }
                }
            }
            clearTable(w1InCommon);
        }
        if (changed) {
            invalidateState();
        }
        return changed;
    }

    private static boolean isNonZeroArea(long[][] area) {
        if (area != null) {
            for (long[] block : area) {
                if (isNonZeroBlock(block)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean isNonZeroBlock(long[] block) {
        if (block != null) {
            for (long word : block) {
                if (word != 0) {
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public boolean andNot(IBitSet set) {
        if (this == set) {
            boolean changed = !isEmpty();
            clear();
            return changed;
        }
        if (!(set instanceof SparseBitSet other)) {
            return super.andNot(set);
        }
        return iterateBlocks(this, other, new AndNotAction(this));
    }

    private static class AndNotAction extends ChangeAction {

        private AndNotAction(SparseBitSet self) {
            super(self);
        }

        @Override
        boolean accept(int w1, int w2, long[] selfBlock, long[] iteratedBlock) {
            boolean isZero = true;
            boolean changed = false;
            if (selfBlock != null) {
                for (int w3 = 0; w3 < LENGTH3; ++w3) {
                    long selfWord = selfBlock[w3];
                    if (selfWord != 0) {
                        long newWord = selfWord & ~iteratedBlock[w3];
                        if (newWord != selfWord) {
                            selfBlock[w3] = newWord;
                            changed = true;
                        }
                        if (newWord != 0) {
                            isZero = false;
                        }
                    }
                }
            }
            this.changed |= changed;
            return isZero;
        }
    }

    @Override
    public boolean or(IBitSet set) {
        if (this == set) {
            return false;
        }
        if (!(set instanceof SparseBitSet other)) {
            return super.or(set);
        }
        return orTable(other.table, null);
    }

    /**
     * {@inheritDoc}
     * <p>
     * With sparse memo sets this works on words: per word of this set, only
     * the bits that are not yet known are tested, and the accepted bits
     * are counted with {@link Long#bitCount}.
     */
    @Override
    public int updateMemoAndCount(IBitSet known, IBitSet pass, IntPredicate test) {
        if (!(known instanceof SparseBitSet k && pass instanceof SparseBitSet p)) {
            return super.updateMemoAndCount(known, pass, test);
        }
        checkMemoSets(known, pass);
        long[][][] selfTable = table;
        int count = 0;
        for (int w1 = 0; w1 < selfTable.length; ++w1) {
            long[][] area = selfTable[w1];
            if (area == null) {
                continue;
            }
            for (int w2 = 0; w2 < LENGTH2; ++w2) {
                long[] block = area[w2];
                if (block == null) {
                    continue;
                }
                long[] knownBlock = getBlock(k.table, w1, w2);
                long[] passBlock = getBlock(p.table, w1, w2);
                for (int w3 = 0; w3 < LENGTH3; ++w3) {
                    long word = block[w3];
                    if (word == 0) {
                        continue;
                    }
                    long unknown = knownBlock == null ? word : word & ~knownBlock[w3];
                    if (unknown != 0) {
                        // tested before they are marked known: a throwing
                        // test leaves the bits of this word unknown
                        long accepted = testBits(unknown, bitIndex(w1, w2, w3), test);
                        if (knownBlock == null) {
                            knownBlock = k.getOrCreateBlock(w1, w2);
                        }
                        knownBlock[w3] |= unknown;
                        k.invalidateState();
                        if (accepted != 0) {
                            if (passBlock == null) {
                                passBlock = p.getOrCreateBlock(w1, w2);
                            }
                            passBlock[w3] |= accepted;
                            p.invalidateState();
                        }
                    }
                    if (passBlock != null) {
                        count += Long.bitCount(word & passBlock[w3]);
                    }
                }
            }
        }
        return count;
    }

    /**
     * @return the bits of {@code word} whose indexes (from {@code base})
     * the predicate accepts, testing them in ascending order.
     */
    private static long testBits(long word, int base, IntPredicate test) {
        long accepted = 0;
        for (long rest = word; rest != 0; rest &= rest - 1) {
            int bit = Long.numberOfTrailingZeros(rest);
            if (test.test(base + bit)) {
                accepted |= 1L << bit;
            }
        }
        return accepted;
    }

    /**
     * {@inheritDoc}
     * <p>
     * With a sparse argument this visits only the blocks present in both
     * sets and the words of their intersection.
     */
    @Override
    public void forEachAnd(IBitSet set, IntConsumer action) {
        if (!(set instanceof SparseBitSet other)) {
            super.forEachAnd(set, action);
            return;
        }
        long[][][] selfTable = table;
        long[][][] otherTable = other.table;
        int areas = Math.min(selfTable.length, otherTable.length);
        for (int w1 = 0; w1 < areas; ++w1) {
            long[][] area = selfTable[w1];
            long[][] otherArea = otherTable[w1];
            if (area == null || otherArea == null) {
                continue;
            }
            for (int w2 = 0; w2 < LENGTH2; ++w2) {
                long[] block = area[w2];
                long[] otherBlock = otherArea[w2];
                if (block == null || otherBlock == null) {
                    continue;
                }
                for (int w3 = 0; w3 < LENGTH3; ++w3) {
                    int base = bitIndex(w1, w2, w3);
                    for (long rest = block[w3] & otherBlock[w3]; rest != 0; rest &= rest - 1) {
                        action.accept(base + Long.numberOfTrailingZeros(rest));
                    }
                }
            }
        }
    }

    @Override
    public IBitSet orDiff(IBitSet set) {
        if (this == set) {
            return new SparseBitSet();
        }
        if (!(set instanceof SparseBitSet other)) {
            return super.orDiff(set);
        }
        SparseBitSet diff = new SparseBitSet();
        if (orTable(other.table, diff)) {
            // orTable writes the blocks of diff directly
            diff.invalidateState();
        }
        return diff;
    }

    /**
     * Ors the blocks of {@code source} into this set, area by area: each area
     * of this set (and of {@code diff}) is fetched or created once, a block of
     * {@code source} whose words are all zero is skipped without touching this
     * set, and a block is allocated only when it receives a non-zero word.
     * The state of this set is updated from each changed word; the caller
     * invalidates the state of {@code diff}.
     *
     * @param source the table of the set to or into this set
     * @param diff   if not {@code null}, a fresh set that receives the bits
     *               this call adds to this set
     * @return {@code true} if this set changed
     */
    private boolean orTable(long[][][] source, @Nullable SparseBitSet diff) {
        boolean changed = false;
        for (int w1 = 0; w1 < source.length; ++w1) {
            long[][] sourceArea = source[w1];
            if (sourceArea == null) {
                continue;
            }
            long[][] selfArea = w1 < table.length ? table[w1] : null;
            long[][] diffArea = null;
            for (int w2 = 0; w2 < LENGTH2; ++w2) {
                long[] sourceBlock = sourceArea[w2];
                if (sourceBlock == null) {
                    continue;
                }
                long[] selfBlock = selfArea != null ? selfArea[w2] : null;
                if (selfBlock == null) {
                    if (!isNonZeroBlock(sourceBlock)) {
                        continue;
                    }
                    if (selfArea == null) {
                        selfArea = getOrCreateArea(w1);
                    }
                    selfBlock = sourceBlock.clone();
                    selfArea[w2] = selfBlock;
                    recordNewBlock(w1, w2, selfBlock);
                    changed = true;
                    if (diff != null) {
                        if (diffArea == null) {
                            diffArea = diff.getOrCreateArea(w1);
                        }
                        diffArea[w2] = sourceBlock.clone();
                    }
                    continue;
                }
                long[] diffBlock = null;
                for (int w3 = 0; w3 < LENGTH3; ++w3) {
                    long sourceWord = sourceBlock[w3];
                    long selfWord = selfBlock[w3];
                    long newWord = selfWord | sourceWord;
                    if (newWord != selfWord) {
                        selfBlock[w3] = newWord;
                        recordWord(wordIndex(w1, w2, w3), selfWord, newWord);
                        changed = true;
                        if (diff != null) {
                            if (diffBlock == null) {
                                if (diffArea == null) {
                                    diffArea = diff.getOrCreateArea(w1);
                                }
                                diffBlock = diffArea[w2] = new long[LENGTH3];
                            }
                            diffBlock[w3] = sourceWord & ~selfWord;
                        }
                    }
                }
            }
        }
        return changed;
    }

    @Override
    public boolean xor(IBitSet set) {
        if (this == set) {
            boolean changed = !isEmpty();
            clear();
            return changed;
        }
        if (!(set instanceof SparseBitSet other)) {
            return super.xor(set);
        }
        return iterateBlocks(this, other, new XorAction(this));
    }

    private static class XorAction extends ChangeAction {

        private XorAction(SparseBitSet self) {
            super(self);
        }

        @Override
        boolean accept(int w1, int w2, long[] selfBlock, long[] iteratedBlock) {
            boolean isZero = true;
            boolean changed = false;
            for (int w3 = 0; w3 < LENGTH3; ++w3) {
                long iteratedWord = iteratedBlock[w3];
                if (iteratedWord != 0) {
                    isZero = false;
                    if (selfBlock == null) {
                        selfBlock = self.getOrCreateBlock(w1, w2);
                    }
                    long selfWord = selfBlock[w3];
                    long newWord = selfWord ^ iteratedWord;
                    if (selfWord != newWord) {
                        selfBlock[w3] = newWord;
                        changed = true;
                    }
                } else if (selfBlock != null && selfBlock[w3] != 0) {
                    isZero = false;
                }
            }
            this.changed |= changed;
            return isZero;
        }
    }

    @Override
    public void clear() {
        clearTable(0);
    }

    @Override
    public boolean isEmpty() {
        updateState();
        return state.cardinality == 0;
    }

    @Override
    public int length() {
        updateState();
        return state.length();
    }

    @Override
    public int size() {
        updateState();
        return state.size();
    }

    @Override
    public int cardinality() {
        updateState();
        return state.cardinality;
    }

    @Override
    public int hashCode() {
        updateState();
        return state.hash();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        SparseBitSet that = (SparseBitSet) o;
        return cardinality() == that.cardinality() && contains(that);
    }

    @Override
    public SparseBitSet copy() {
        SparseBitSet copy = new SparseBitSet();
        copy.or(this);
        return copy;
    }

    /**
     * Packs the bits of this set into one array that holds only its non-zero
     * words: for each block with a non-zero word, in ascending block order,
     * a header {@code (blockIndex << 32) | wordMask} (bit {@code w3} of the
     * mask set when word {@code w3} of the block is non-zero), followed by
     * the non-zero words of the block in ascending order.
     * {@link #ofPacked(long[])} restores an equal set.
     *
     * @return the packed words; empty when this set is empty
     */
    public long[] toPacked() {
        int length = 0;
        for (long[][] area : table) {
            if (area != null) {
                for (long[] block : area) {
                    int words = block == null ? 0 : nonZeroWords(block);
                    if (words != 0) {
                        length += 1 + words;
                    }
                }
            }
        }
        long[] packed = new long[length];
        int at = 0;
        for (int w1 = 0; w1 < table.length; ++w1) {
            long[][] area = table[w1];
            if (area == null) {
                continue;
            }
            for (int w2 = 0; w2 < LENGTH2; ++w2) {
                long[] block = area[w2];
                if (block == null) {
                    continue;
                }
                int header = at;
                long mask = 0;
                for (int w3 = 0; w3 < LENGTH3; ++w3) {
                    if (block[w3] != 0) {
                        mask |= 1L << w3;
                        packed[++at] = block[w3];
                    }
                }
                if (mask != 0) {
                    packed[header] = ((long) ((w1 << LEVEL2) + w2) << Integer.SIZE) | mask;
                    ++at;
                }
            }
        }
        return packed;
    }

    /**
     * Restores a set from the array written by {@link #toPacked()}.
     *
     * @param packed the packed words
     * @return a new set equal to the packed one
     */
    public static SparseBitSet ofPacked(long[] packed) {
        SparseBitSet set = new SparseBitSet();
        int at = 0;
        while (at < packed.length) {
            long header = packed[at++];
            int blockIndex = (int) (header >>> Integer.SIZE);
            int mask = (int) header;
            long[] block = set.getOrCreateBlock(blockIndex >> LEVEL2, blockIndex & MASK2);
            for (int w3 = 0; w3 < LENGTH3; ++w3) {
                if ((mask & (1 << w3)) != 0) {
                    block[w3] = packed[at++];
                }
            }
        }
        set.invalidateState();
        return set;
    }

    private static int nonZeroWords(long[] block) {
        int words = 0;
        for (long word : block) {
            if (word != 0) {
                ++words;
            }
        }
        return words;
    }

    // ------------------------------------------------------------------------
    // utility methods and classes
    // ------------------------------------------------------------------------

    /**
     * Extracts level 1 index (i.e., area index) from {@code wordIndex}.
     */
    private static int level1Index(int wordIndex) {
        return wordIndex >> SHIFT1;
    }

    /**
     * Extracts level 2 index (i.e., block index) from {@code wordIndex}.
     */
    private static int level2Index(int wordIndex) {
        return (wordIndex >> SHIFT2) & MASK2;
    }

    /**
     * Extracts level 3 index (i.e., word index in the block) from {@code wordIndex}.
     */
    private static int level3Index(int wordIndex) {
        return wordIndex & MASK3;
    }

    /**
     * Combines level 1/2/3 indexes to compute the corresponding word index.
     */
    private static int wordIndex(int w1, int w2, int w3) {
        return (w1 << SHIFT1) + (w2 << SHIFT2) + w3;
    }

    /**
     * Combines level 1/2/3 indexes to compute the corresponding bit index.
     *
     * @return index of the first bit in the word specified by the combined word index
     */
    private static int bitIndex(int w1, int w2, int w3) {
        return wordIndex(w1, w2, w3) << SHIFT3;
    }

    /**
     * Retrieves the block of specified position in the given table.
     *
     * @param table the table
     * @param w1    level 1 index
     * @param w2    level 2 index
     * @return the block if it is present in the table, or {@code null} if absent.
     */
    private static long @Nullable [] getBlock(long[][][] table, int w1, int w2) {
        return w1 < table.length && table[w1] != null ? table[w1][w2] : null;
    }

    /**
     * Retrieves the block of specified position in the table of this set.
     * If the block is absent (i.e., {@code null}), this method will create
     * the block, and resize table and create new area, if necessary.
     */
    private long[] getOrCreateBlock(int w1, int w2) {
        long[][] area = getOrCreateArea(w1);
        long[] block;
        if ((block = area[w2]) == null) {
            block = area[w2] = new long[LENGTH3];
        }
        return block;
    }

    /**
     * Retrieves the area of specified position in the table of this set.
     * If the area is absent (i.e., {@code null}), this method will create
     * the area, and resize table, if necessary.
     */
    private long[][] getOrCreateArea(int w1) {
        if (w1 >= table.length) {
            resize(bitIndex(w1, /* only the highest one bit matters */ 0, 0));
        }
        long[][] area;
        if ((area = table[w1]) == null) {
            area = table[w1] = new long[LENGTH2][];
        }
        return area;
    }

    /**
     * Resize the bit array. Moves the entries in the bits array of this
     * SparseBitSet into an array whose size (which may be larger or smaller)
     * is the given bit size (<i>i.e.</i>, includes the bit whose bitIndex is
     * one less that the given value). If the new array is smaller, the excess
     * entries in the set array are discarded. If the new array is bigger,
     * it is filled with nulls.
     *
     * @param bitIndex the desired bit index to be included in the set
     */
    private void resize(int bitIndex) {
        //  Find an array size that is a power of two that is as least
        //  large enough to contain the bitIndex requested.
        final int w1 = level1Index(wordIndex(bitIndex));
        int newSize = Integer.highestOneBit(w1);
        if (newSize == 0) {
            newSize = 1;
        }
        if (w1 >= newSize) {
            newSize <<= 1;
        }
        if (newSize > MAX_LENGTH1) {
            newSize = MAX_LENGTH1;
        }
        final int aLength1 = (table != null ? table.length : 0);

        if (newSize != aLength1 || table == null) {
            // only if the size needs to be changed
            final long[][][] temp = new long[newSize][][]; //  Get the new array
            if (aLength1 != 0) {
                //  If it exists, copy old array to the new array.
                System.arraycopy(table, 0, temp, 0, Math.min(aLength1, newSize));
                clearTable(0); //  Don't leave unused pointers around.
            }
            table = temp; //  Set new array as the set array
            bitsLength = //  Index of last possible bit, plus one.
                    (newSize == MAX_LENGTH1 ? Integer.MAX_VALUE : newSize * UNIT);
        }
    }

    /**
     * Clears out a part of the set array with nulls, from the given
     * fromAreaIndex to the end of the array. If the given parameter
     * is beyond the end of the bits array, nothing is changed.
     *
     * @param fromAreaIndex word index at which to start (inclusive)
     */
    private void clearTable(int fromAreaIndex) {
        final int aLength = table.length;
        if (fromAreaIndex < aLength) {
            for (int w = fromAreaIndex; w != aLength; ++w) {
                table[w] = null;
            }
            invalidateState();
        }
    }

    /**
     * Core method for set operations. This method operates on two sets,
     * a self set and an iterated set.
     * Note that it ONLY iterates non-null blocks in the iterated set.
     *
     * @param self     the self set
     * @param iterated the other set, whose non-null blocks are iterated
     * @param action   the action to be taken during iteration
     * @param <R>      type of returned value
     * @return result of the action
     */
    private static <R> R iterateBlocks(SparseBitSet self, SparseBitSet iterated,
                                       BlockAction<R> action) {
        assert self == action.self;
        long[][][] selfTable = self.table;
        long[][][] iteratedTable = iterated.table;
        action.start(iterated);
        boolean canIterateBothSets = action.isIterateBothSets();
        outer:
        for (int w1 = 0; w1 < iteratedTable.length; ++w1) {
            // search for non-null areas in iteratedTable
            long[][] iteratedArea = iteratedTable[w1];
            if (iteratedArea != null) {
                boolean isZeroArea = true;
                for (int w2 = 0; w2 < LENGTH2; ++w2) {
                    // search for non-null blocks in iteratedTable
                    long[] iteratedBlock = iteratedArea[w2];
                    if (iteratedBlock != null) {
                        long[] selfBlock = getBlock(selfTable, w1, w2);
                        boolean isZeroBlock = action.accept(w1, w2,
                                selfBlock, iteratedBlock);
                        if (isZeroBlock) {
                            if (selfBlock != null) {
                                // clear zero block in self
                                selfTable[w1][w2] = null;
                                self.invalidateState();
                            }
                        } else { // found non-zero block, then the area is not zero
                            isZeroArea = false;
                        }
                        if (action.canBreak()) {
                            break outer;
                        }
                    }
                }
                if (isZeroArea &&
                        canIterateBothSets && // we can confirm the area is zero
                        // only when non-null blocks of both sets were iterated
                        w1 < selfTable.length && selfTable[w1] != null) {
                    // clear zero area in self
                    selfTable[w1] = null;
                    self.invalidateState();
                }
            }
        }
        action.finish();
        return action.getResult();
    }

    /**
     * Actions that are performed during iterating non-null blocks.
     *
     * @param <R> type of return valued
     */
    private abstract static class BlockAction<R> {

        final SparseBitSet self;

        BlockAction(SparseBitSet self) {
            this.self = self;
        }

        /**
         * Operation needs to be performed before the iteration.
         */
        void start(SparseBitSet iterated) {
        }

        /**
         * @return {@code true} if {@code selfBlock} becomes zero block after
         * this call.
         */
        abstract boolean accept(int w1, int w2, long[] selfBlock, long[] iteratedBlock);

        /**
         * @return whether this action iterates both self set and the other set.
         */
        boolean isIterateBothSets() {
            return false;
        }

        /**
         * @return whether the iteration can be broken.
         */
        boolean canBreak() {
            return false;
        }

        /**
         * Operation needs to be performed after the iteration.
         */
        void finish() {
        }

        /**
         * @return the result of iteration.
         */
        R getResult() {
            return null;
        }
    }

    /**
     * Abstract class for the actions that may change {@code self} set.
     */
    private abstract static class ChangeAction extends BlockAction<Boolean> {

        boolean changed;

        private ChangeAction(SparseBitSet self) {
            super(self);
        }

        @Override
        void start(SparseBitSet iterated) {
            changed = false;
        }

        @Override
        void finish() {
            if (changed) {
                self.invalidateState();
            }
        }

        @Override
        Boolean getResult() {
            return changed;
        }
    }

    private void invalidateState() {
        state.valid = false;
    }

    /**
     * Updates the state for a block that was just added to this set and that
     * receives at least one non-zero word before this set is read again.
     * Words of the block are recorded separately.
     */
    private void recordNewBlock() {
        State s = state;
        if (s.valid) {
            if (s.incremental) {
                ++s.blockCount;
            } else {
                s.valid = false;
            }
        }
    }

    /**
     * Updates the state for a non-zero block that was just added to this set
     * at the given position, together with its words.
     */
    private void recordNewBlock(int w1, int w2, long[] block) {
        recordNewBlock();
        if (state.valid) {
            for (int w3 = 0; w3 < LENGTH3; ++w3) {
                long word = block[w3];
                if (word != 0) {
                    recordWord(wordIndex(w1, w2, w3), 0L, word);
                }
            }
        }
    }

    /**
     * Updates the state for a word that only gained bits: {@code newWord}
     * holds every bit of {@code oldWord} and at least one more.
     * The update gives what {@link #updateState()} would compute for the
     * changed set, as the hash is a xor over the words and the other values
     * are counts and the last non-zero word. It is done only while the state
     * is valid and {@link State#incremental}; otherwise the state is
     * invalidated.
     *
     * @param index   the word index of the changed word
     * @param oldWord the word before the change
     * @param newWord the word after the change
     */
    private void recordWord(int index, long oldWord, long newWord) {
        State s = state;
        if (!s.valid) {
            return;
        }
        if (!s.incremental) {
            s.valid = false;
            return;
        }
        long weight = index + 1;
        s.rawHash ^= (oldWord * weight) ^ (newWord * weight);
        s.cardinality += Long.bitCount(newWord) - Long.bitCount(oldWord);
        if (oldWord == 0) {
            ++s.count;
        }
        // an empty set has maxWordIndex 0, so its first word passes here
        if (index >= s.maxWordIndex) {
            s.maxWordIndex = index;
            s.maxWord = newWord;
        }
    }

    /**
     * The entirety of the bit set is examined, and the various statistics of
     * the bit set (size, length, cardinality, hashCode, etc.) are computed. Level
     * arrays that are empty (i.e., all zero at level 3, all null at level 2) are
     * replaced by null references, ensuring a normalized representation.
     */
    private void updateState() {
        if (!state.valid) {
            iterateBlocks(this, this, new UpdateAction(this));
        }
    }

    @Serial
    private void writeObject(ObjectOutputStream s) throws IOException {
        updateState(); // Update structure and state if needed.
        /* Write any hidden stuff. */
        s.defaultWriteObject();
        s.writeInt(state.length()); // Needed to know where last bit is

        /* This is the number of index/value pairs to be written. */
        int count = state.count; // Minimum number of words to be written
        s.writeInt(count);
        final long[][][] a1 = table;
        final int aLength1 = a1.length;
        long[][] a2;
        long[] a3;
        long word;
        for (int w1 = 0; w1 != aLength1; ++w1) {
            if ((a2 = a1[w1]) != null) {
                for (int w2 = 0; w2 != LENGTH2; ++w2) {
                    if ((a3 = a2[w2]) != null) {
                        final int base = (w1 << SHIFT1) + (w2 << SHIFT2);
                        for (int w3 = 0; w3 != LENGTH3; ++w3) {
                            if ((word = a3[w3]) != 0) {
                                s.writeInt(base + w3);
                                s.writeLong(word);
                                --count;
                            }
                        }
                    }
                }
            }
        }
        if (count != 0) {
            throw new InternalError("count of entries not consistent");
        }
        /* As a consistency check, write the hash code of the set. */
        s.writeInt(state.hash());
    }

    @Serial
    private void readObject(ObjectInputStream s) throws IOException,
            ClassNotFoundException {
        /* Read in any hidden stuff that is part of the class overhead. */
        s.defaultReadObject();
        final int aLength = s.readInt();
        resize(aLength); // Make sure there is enough space

        /* Read in number of mappings. */
        final int count = s.readInt();
        /* Read the keys and values, them into the set array, areas, and blocks. */
        long[][] a2;
        long[] a3;
        for (int n = 0; n != count; ++n) {
            final int w = s.readInt();
            final int w3 = w & MASK3;
            final int w2 = (w >> SHIFT2) & MASK2;
            final int w1 = w >> SHIFT1;

            final long word = s.readLong();
            if ((a2 = table[w1]) == null) {
                a2 = table[w1] = new long[LENGTH2][];
            }
            if ((a3 = a2[w2]) == null) {
                a3 = a2[w2] = new long[LENGTH3];
            }
            a3[w3] = word;
        }
        /* Ensure all the pieces are set up for set scanning. */
        state = new State();
        updateState();
        if (count != state.count) {
            throw new InternalError("count of entries not consistent");
        }
        final int hash = s.readInt(); // Get the hashcode that was stored
        if (hash != state.hash()) { // An error of some kind, if not the same
            throw new IOException("deserialized hashCode mis-match");
        }
    }

    private static class UpdateAction extends BlockAction<Void> {

        /**
         * Working space for find the size and length of the bit set. Holds the
         * index of the last non-empty word in the set.
         */
        private transient int maxWordIndex;

        /**
         * Working space for find the size and length of the bit set. Holds a copy
         * of the last non-empty word in the set.
         */
        private transient long maxWord;

        /**
         * Working space for find the hash value of the bit set. Holds the
         * current state of the computation of the hash value. This value is
         * ultimately transferred to the Cache object.
         *
         * @see State
         */
        private transient long hash;

        /**
         * Working space for keeping count of the number of non-zero words in the
         * bit set. Holds the current state of the computation of the count. This
         * value is ultimately transferred to the Cache object.
         *
         * @see State
         */
        private transient int count;

        /**
         * Number of blocks actually in use by this set to represent bit values.
         */
        private transient int blockCount;

        /**
         * Number of the visited blocks whose words are all zero. They are
         * counted in {@link #blockCount} and then removed from the set.
         */
        private transient int zeroBlockCount;

        /**
         * Working space for counting the number of non-zero bits in the bit set.
         * Holds the current state of the computation of the cardinality.This
         * value is ultimately transferred to the Cache object.
         *
         * @see State
         */
        private transient int cardinality;

        private UpdateAction(SparseBitSet self) {
            super(self);
        }

        @Override
        void start(SparseBitSet iterated) {
            hash = 1234L; // Magic number
            maxWordIndex = 0; // index of last non-zero word
            maxWord = 0L; // word at that index
            count = 0; // count of non-zero words in whole set
            blockCount = 0; // count of blocks actually use in whole set
            zeroBlockCount = 0; // count of all-zero blocks among them
            cardinality = 0; // count of non-zero bits in the whole set
        }

        @Override
        boolean accept(int w1, int w2, long[] selfBlock, long[] iteratedBlock) {
            ++blockCount;
            boolean isZero = true; //  Presumption
            for (int w3 = 0; w3 != LENGTH3; ++w3) {
                final long word = iteratedBlock[w3];
                if (word != 0) {
                    isZero = false;
                    compute(wordIndex(w1, w2, w3), word);
                }
            }
            if (isZero) {
                ++zeroBlockCount;
            }
            return isZero;
        }

        /**
         * This method does the accumulation of the statistics. It must be called
         * in sequential order of the words in the set for which the statistics
         * are being accumulated, and only for non-null values of the second
         * parameter.
         * <p>
         * Two of the values (a2Count and a3Count) are not updated here,
         * but are done in the code near where this method is called.
         *
         * @param index the word index of the word supplied
         * @param word  the long non-zero word from the set
         */
        private void compute(final int index, final long word) {
            // Count the number of actual words being used.
            ++count;
            // Continue to accumulate the hash value of the set.
            hash ^= word * (long) (index + 1);
            // The last non-zero word contains the last actual bit of the set.
            // The location of this bit is used to compute the set length.
            maxWordIndex = index;
            maxWord = word;
            // Count the actual bits, so as to get the cardinality of the set.
            cardinality += Long.bitCount(word);
        }

        @Override
        boolean isIterateBothSets() {
            return true;
        }

        @Override
        void finish() {
            State state = self.state;
            state.count = count;
            state.cardinality = cardinality;
            state.maxWordIndex = maxWordIndex;
            state.maxWord = maxWord;
            state.blockCount = blockCount;
            state.rawHash = hash;
            // the size counts the all-zero blocks this pass removed, so a
            // later update word by word must not start from it
            state.incremental = zeroBlockCount == 0;
            state.valid = true;
        }
    }

    private static class State {

        /**
         * Boolean value indicating whether the values in current state is valid;
         * if not, then {@link #updateState()} should be called to update.
         */
        private boolean valid;

        /**
         * Whether a valid state may be updated word by word
         * ({@link #recordWord}, {@link #recordNewBlock()}). Set by
         * {@link #updateState()} only when it found no all-zero block; while
         * it holds, the set has no all-zero block, because every writer that
         * can leave one invalidates the state.
         */
        private boolean incremental;

        /** The hash before folding to an {@code int}. */
        private transient long rawHash;

        /** Number of blocks in use; all-zero blocks a recompute removed included. */
        private transient int blockCount;

        private transient int cardinality;

        /** Index of the last non-zero word, or 0 if there is none. */
        private transient int maxWordIndex;

        /** The last non-zero word, or 0 if there is none. */
        private transient long maxWord;

        private transient int count;

        private int hash() {
            return (int) ((rawHash >> Integer.SIZE) ^ rawHash);
        }

        private int size() {
            return blockCount * LENGTH3 * BITS_PER_WORD;
        }

        private int length() {
            return (maxWordIndex + 1) * BITS_PER_WORD - Long.numberOfLeadingZeros(maxWord);
        }
    }
}
