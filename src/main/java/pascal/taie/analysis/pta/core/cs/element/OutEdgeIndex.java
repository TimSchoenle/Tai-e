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
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;

/**
 * Membership of the out-edge targets of an {@link AbstractPointer}, read
 * from its out-edge array ({@link AbstractPointer#SLOTS} slots per entry,
 * the target or the edge object in the first slot of each entry).
 * <p>
 * An edge array of at most {@link #LINEAR_ENTRIES} entries has no index:
 * its entries are scanned. A larger one has an open-addressing table of
 * entry numbers plus one (0 marks a free slot), sized for the capacity of
 * the edge array at load 0.85 at most, of the narrowest element type that
 * holds the entry numbers ({@code byte[]} up to 255 entries,
 * {@code char[]} up to 65,535, {@code int[]} above). The table holds the
 * first entry of each target; the target of a slot is read from the edge
 * array, so the table is rebuilt whenever the edge array is replaced.
 */
final class OutEdgeIndex {

    /**
     * Largest edge-array capacity, in entries, that is scanned instead of
     * indexed.
     */
    static final int LINEAR_ENTRIES = 8;

    private static final int MAX_LOAD_NUMERATOR = 17;

    private static final int MAX_LOAD_DENOMINATOR = 20;

    private static final int HASH_MULTIPLIER = 0x9E3779B9;

    private static final int BYTE_ENTRIES = 0xFF;

    private static final int CHAR_ENTRIES = 0xFFFF;

    /**
     * Bytes to which array payloads are padded (object alignment).
     */
    private static final int ALIGNMENT = 8;

    private OutEdgeIndex() {
    }

    /**
     * @return the index of the target of entry {@code entry}.
     */
    static int targetIndex(Object[] slots, int entry) {
        Object first = slots[entry * AbstractPointer.SLOTS];
        return first instanceof PointerFlowEdge edge
                ? edge.target().getIndex() : ((Pointer) first).getIndex();
    }

    /**
     * @param slots   the edge array
     * @param entries the number of entries in use
     * @return the table for the edge array, holding the first entry of each
     * target among the entries in use, or null if the edge array has at
     * most {@link #LINEAR_ENTRIES} entries.
     */
    static @Nullable Object build(Object[] slots, int entries) {
        int capacity = slots.length / AbstractPointer.SLOTS;
        if (capacity <= LINEAR_ENTRIES) {
            return null;
        }
        int needed = (int) (((long) capacity * MAX_LOAD_DENOMINATOR + MAX_LOAD_NUMERATOR - 1)
                / MAX_LOAD_NUMERATOR);
        Object table;
        if (capacity <= BYTE_ENTRIES) {
            table = new byte[roundUp(needed, ALIGNMENT)];
        } else if (capacity <= CHAR_ENTRIES) {
            table = new char[roundUp(needed, ALIGNMENT / Character.BYTES)];
        } else {
            table = new int[roundUp(needed, ALIGNMENT / Integer.BYTES)];
        }
        for (int entry = 0; entry < entries; entry++) {
            int slot = probe(table, slots, targetIndex(slots, entry));
            if (get(table, slot) == 0) {
                set(table, slot, entry + 1);
            }
        }
        return table;
    }

    /**
     * @param table the table of the edge array, or null if it has none
     * @param slots the edge array, or null if there is none
     * @return whether an entry in use has the target {@code target}.
     */
    static boolean contains(@Nullable Object table, Object @Nullable [] slots, int target) {
        if (slots == null) {
            return false;
        }
        if (table == null) {
            for (int i = 0; i < slots.length && slots[i] != null; i += AbstractPointer.SLOTS) {
                if (targetIndex(slots, i / AbstractPointer.SLOTS) == target) {
                    return true;
                }
            }
            return false;
        }
        return get(table, probe(table, slots, target)) != 0;
    }

    /**
     * Adds entry {@code entry}, whose target no other entry has, to the
     * table.
     */
    static void insert(Object table, Object[] slots, int entry) {
        set(table, probe(table, slots, targetIndex(slots, entry)), entry + 1);
    }

    /**
     * @return the slot of the table that holds the first entry with the
     * target, or the free slot where it belongs.
     */
    private static int probe(Object table, Object[] slots, int target) {
        // one type test per probe, then a loop over the typed table
        if (table instanceof byte[] bytes) {
            int length = bytes.length;
            int i = home(target, length);
            while (true) {
                int value = bytes[i] & BYTE_ENTRIES;
                if (value == 0 || targetIndex(slots, value - 1) == target) {
                    return i;
                }
                if (++i == length) {
                    i = 0;
                }
            }
        } else if (table instanceof char[] chars) {
            int length = chars.length;
            int i = home(target, length);
            while (true) {
                int value = chars[i];
                if (value == 0 || targetIndex(slots, value - 1) == target) {
                    return i;
                }
                if (++i == length) {
                    i = 0;
                }
            }
        }
        int[] ints = (int[]) table;
        int length = ints.length;
        int i = home(target, length);
        while (true) {
            int value = ints[i];
            if (value == 0 || targetIndex(slots, value - 1) == target) {
                return i;
            }
            if (++i == length) {
                i = 0;
            }
        }
    }

    /**
     * @return the high bits of the 32-bit hash of the target, scaled to
     * [0, length).
     */
    private static int home(int target, int length) {
        return (int) (((target * HASH_MULTIPLIER) & 0xFFFF_FFFFL) * length >>> 32);
    }

    private static int roundUp(int length, int multiple) {
        return (length + multiple - 1) / multiple * multiple;
    }

    private static int get(Object table, int i) {
        if (table instanceof byte[] bytes) {
            return bytes[i] & BYTE_ENTRIES;
        } else if (table instanceof char[] chars) {
            return chars[i];
        }
        return ((int[]) table)[i];
    }

    private static void set(Object table, int i, int value) {
        if (table instanceof byte[] bytes) {
            bytes[i] = (byte) value;
        } else if (table instanceof char[] chars) {
            chars[i] = (char) value;
        } else {
            ((int[]) table)[i] = value;
        }
    }
}
