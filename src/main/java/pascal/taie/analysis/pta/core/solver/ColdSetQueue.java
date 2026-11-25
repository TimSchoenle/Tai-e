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

package pascal.taie.analysis.pta.core.solver;

import pascal.taie.analysis.pta.core.cs.element.Pointer;

import java.util.Arrays;
import java.util.function.Consumer;

/**
 * A first-in first-out window over the pointers whose sets were written
 * last (option {@code pack-cold-sets}). A pointer whose set is written
 * enters the window; when the window holds more than its size, the oldest
 * entries leave it, and {@link #drain} hands over each pointer whose set
 * had no write since that entry, so that its owner can store the set in a
 * packed form. A pointer written again keeps only its newest entry live.
 * <p>
 * Entries leave the window only in {@link #drain}, which the solver calls
 * at a point where no caller holds a set of a pointer in its unpacked form;
 * between two drains the window grows by the writes made in between.
 * Each pointer's newest entry is told by a stamp kept by pointer index;
 * after 2^32 writes the stamps wrap, which can at worst let an old entry
 * hand a pointer over early: packing keeps a set's contents, so that costs
 * only a restore.
 */
final class ColdSetQueue {

    private static final int INITIAL_CAPACITY = 16;

    /**
     * The stamp of no live entry; never given to an entry.
     */
    private static final int NONE = 0;

    private final int window;

    /**
     * The entries in a ring: pointer and stamp, oldest at {@code head}.
     */
    private Pointer[] pointers = new Pointer[INITIAL_CAPACITY];

    private int[] stamps = new int[INITIAL_CAPACITY];

    private int head;

    private int size;

    /**
     * The stamp of each pointer's newest live entry, by pointer index.
     */
    private int[] liveStamps = new int[INITIAL_CAPACITY];

    private int clock;

    /**
     * @param window the number of newest entries that stay in the window,
     *               at least 1
     */
    ColdSetQueue(int window) {
        if (window < 1) {
            throw new IllegalArgumentException("window must be at least 1: " + window);
        }
        this.window = window;
    }

    /**
     * Records a write of the set of {@code pointer}: the pointer enters
     * the window as its newest entry.
     */
    void touch(Pointer pointer) {
        int stamp = ++clock;
        if (stamp == NONE) {
            stamp = ++clock;
        }
        int index = pointer.getIndex();
        if (index >= liveStamps.length) {
            liveStamps = Arrays.copyOf(liveStamps,
                    Math.max(index + 1, liveStamps.length + (liveStamps.length >> 1)));
        }
        liveStamps[index] = stamp;
        if (size == pointers.length) {
            growRing();
        }
        int slot = (head + size) & (pointers.length - 1);
        pointers[slot] = pointer;
        stamps[slot] = stamp;
        ++size;
    }

    /**
     * Drops the live entry of {@code pointer}, if any: its set is not
     * handed over when that entry leaves the window.
     */
    void forget(Pointer pointer) {
        int index = pointer.getIndex();
        if (index < liveStamps.length) {
            liveStamps[index] = NONE;
        }
    }

    /**
     * Removes the entries beyond the newest {@code window} ones, oldest
     * first, and hands each pointer whose removed entry was live to
     * {@code pack}.
     */
    void drain(Consumer<Pointer> pack) {
        while (size > window) {
            int slot = head;
            Pointer pointer = pointers[slot];
            int stamp = stamps[slot];
            pointers[slot] = null;
            head = (head + 1) & (pointers.length - 1);
            --size;
            int index = pointer.getIndex();
            if (liveStamps[index] == stamp) {
                liveStamps[index] = NONE;
                pack.accept(pointer);
            }
        }
    }

    /**
     * @return the number of entries, live or not.
     */
    int size() {
        return size;
    }

    private void growRing() {
        int capacity = pointers.length;
        Pointer[] newPointers = new Pointer[capacity * 2];
        int[] newStamps = new int[capacity * 2];
        for (int i = 0; i < size; ++i) {
            int slot = (head + i) & (capacity - 1);
            newPointers[i] = pointers[slot];
            newStamps[i] = stamps[slot];
        }
        pointers = newPointers;
        stamps = newStamps;
        head = 0;
    }
}
