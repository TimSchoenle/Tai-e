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

/**
 * The sources of the edges in the slots of a hashed {@link CallSiteEdges}
 * table, one per slot, null for a slot without a sourced edge. A call site
 * has few distinct sources, so a slot holds a code into a dictionary of the
 * distinct sources set so far: a byte per slot while at most
 * {@value #BYTE_LIMIT} distinct sources are held, then a char per slot.
 * A new distinct source is refused (see {@link #set}) when the dictionary
 * would hold more than {@value #CHAR_LIMIT} sources, or when the column
 * with it (codes, dictionary and lookup table, see {@link #bytes}) would
 * take more bytes than an {@code EdgeSource[]} of its slots; the owner then
 * keeps the sources in such an array (see {@link #toArray}).
 * <p>
 * The dictionary is keyed by identity, so {@link #get} returns the very
 * object that {@link #set} received for that slot: the column is exact
 * whatever {@link EdgeSource#equals} does.
 */
final class SourceColumn {

    private static final int BYTE_LIMIT = 255;

    private static final int CHAR_LIMIT = 65535;

    /**
     * Up to this many distinct sources, a source is looked up by a linear
     * scan of the dictionary; above, by {@link #lookup}.
     */
    private static final int LINEAR_LIMIT = 8;

    private static final byte[] NO_BYTES = {};

    private static final char[] NO_CHARS = {};

    private static final int[] NO_LOOKUP = {};

    /**
     * Estimated bytes of a column object itself: header and fields.
     */
    private static final int OBJECT_BYTES = 48;

    private final int capacity;

    /**
     * Whether the codes are in {@link #chars} rather than {@link #bytes}.
     */
    private boolean wide;

    /**
     * The codes while not {@link #wide}, unsigned; empty once wide.
     */
    private byte[] bytes;

    /**
     * The codes once {@link #wide}; empty before.
     */
    private char[] chars = NO_CHARS;

    /**
     * The distinct sources by code; index 0 (no source) is unused.
     */
    private EdgeSource[] dict = new EdgeSource[4];

    /**
     * Number of distinct sources in {@link #dict}, which is also the
     * highest code.
     */
    private int distinct;

    /**
     * The code found last by {@link #codeOf}, tried first by the next.
     */
    private int lastCode;

    /**
     * Open-addressing table of codes (0 for a free slot) on the hash codes
     * of their sources; empty while at most {@value #LINEAR_LIMIT} distinct
     * sources are held.
     */
    private int[] lookup = NO_LOOKUP;

    /**
     * Creates a column of {@code capacity} slots without sources.
     */
    SourceColumn(int capacity) {
        this.capacity = capacity;
        this.bytes = new byte[capacity];
    }

    /**
     * @return the source of {@code slot}, or null if it has none.
     */
    @Nullable
    EdgeSource get(int slot) {
        int code = wide ? chars[slot] : bytes[slot] & 0xFF;
        return code == 0 ? null : dict[code];
    }

    /**
     * Sets the source of {@code slot} to {@code source}, unless
     * {@code source} would be a new distinct source beyond the limits of
     * the dictionary; then the column is left unchanged.
     *
     * @return whether the source was set
     */
    boolean set(int slot, EdgeSource source) {
        int code = codeOf(source);
        if (code == 0) {
            return false;
        }
        // codeOf may have widened the codes
        if (wide) {
            chars[slot] = (char) code;
        } else {
            bytes[slot] = (byte) code;
        }
        return true;
    }

    /**
     * @return a new {@code EdgeSource[]} of the sources of the slots.
     */
    EdgeSource[] toArray() {
        EdgeSource[] sources = new EdgeSource[capacity];
        for (int i = 0; i < capacity; ++i) {
            sources[i] = get(i);
        }
        return sources;
    }

    /**
     * @return the estimated bytes of this column with its arrays.
     */
    long bytes() {
        return bytes(wide, dict.length, lookup.length);
    }

    /**
     * @return the code of {@code source}, added to the dictionary if it is
     * not there (widening the codes if the new code requires it); 0 if it
     * is not there and the dictionary is full.
     */
    private int codeOf(EdgeSource source) {
        if (dict[lastCode] == source) {
            return lastCode;
        }
        int code = find(source);
        if (code == 0) {
            code = add(source);
            if (code == 0) {
                return 0;
            }
        }
        lastCode = code;
        return code;
    }

    /**
     * @return the code of {@code source}, or 0 if it is not in the
     * dictionary.
     */
    private int find(EdgeSource source) {
        if (lookup.length == 0) {
            for (int code = 1; code <= distinct; ++code) {
                if (dict[code] == source) {
                    return code;
                }
            }
            return 0;
        }
        int mask = lookup.length - 1;
        int i = spread(source) & mask;
        int code;
        while ((code = lookup[i]) != 0) {
            if (dict[code] == source) {
                return code;
            }
            i = (i + 1) & mask;
        }
        return 0;
    }

    /**
     * Adds {@code source}, which is not in the dictionary, and widens the
     * codes if the new code requires it.
     *
     * @return the new code; 0, with nothing changed, if the dictionary is
     * full
     */
    private int add(EdgeSource source) {
        int code = distinct + 1;
        if (code > CHAR_LIMIT) {
            return 0;
        }
        boolean widen = code > BYTE_LIMIT && !wide;
        int dictLength = code == dict.length
                ? Math.min(CHAR_LIMIT + 1, dict.length * 2)
                : dict.length;
        boolean rebuild = code > LINEAR_LIMIT && code * 2 > lookup.length;
        int lookupLength = rebuild ? Integer.highestOneBit(code) * 4 : lookup.length;
        if (bytes(wide || widen, dictLength, lookupLength)
                > EdgeSourceCensus.arrayBytes(capacity, 4)) {
            return 0;
        }
        if (widen) {
            toChars();
        }
        if (dictLength != dict.length) {
            EdgeSource[] grown = new EdgeSource[dictLength];
            System.arraycopy(dict, 0, grown, 0, dict.length);
            dict = grown;
        }
        dict[code] = source;
        distinct = code;
        if (rebuild) {
            rebuildLookup(lookupLength);
        } else if (code > LINEAR_LIMIT) {
            insertLookup(code);
        }
        return code;
    }

    /**
     * @return the estimated bytes of a column of {@link #capacity} slots
     * with char codes if {@code wideCodes}, else byte codes, a dictionary
     * of {@code dictLength} and a lookup table of {@code lookupLength}.
     */
    private long bytes(boolean wideCodes, int dictLength, int lookupLength) {
        return OBJECT_BYTES
                + EdgeSourceCensus.arrayBytes(capacity, wideCodes ? 2 : 1)
                + EdgeSourceCensus.arrayBytes(dictLength, 4)
                + EdgeSourceCensus.arrayBytes(lookupLength, 4);
    }

    private void rebuildLookup(int length) {
        lookup = new int[length];
        for (int code = 1; code <= distinct; ++code) {
            insertLookup(code);
        }
    }

    private void insertLookup(int code) {
        int mask = lookup.length - 1;
        int i = spread(dict[code]) & mask;
        while (lookup[i] != 0) {
            i = (i + 1) & mask;
        }
        lookup[i] = code;
    }

    private static int spread(EdgeSource source) {
        int h = source.hashCode();
        return h ^ (h >>> 16);
    }

    private void toChars() {
        char[] codes = new char[capacity];
        for (int i = 0; i < capacity; ++i) {
            codes[i] = (char) (bytes[i] & 0xFF);
        }
        chars = codes;
        bytes = NO_BYTES;
        wide = true;
    }
}
