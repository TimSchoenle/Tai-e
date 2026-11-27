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

import org.jspecify.annotations.Nullable;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CallHub;
import pascal.taie.ir.stmt.Invoke;

/**
 * The call hubs of one solve by key (invoke, set of callee nodes): open
 * addressing over the hubs with their cached hashes, load at most 1/2. A
 * key is equal only with the same invoke and the same node set, compared
 * node by node, never by hash alone: a hub found by hash only could give a
 * call site the edges of another node set. Never iterated for output.
 */
final class CallHubTable {

    private CallHub[] slots = new CallHub[64];

    private int size;

    /**
     * Hash function of the table; {@link CallHub#hashOf} except in tests.
     */
    interface Hasher {
        int hash(Invoke invoke, CSMethod[] nodes, int size);
    }

    private final Hasher hasher;

    CallHubTable() {
        this(CallHub::hashOf);
    }

    CallHubTable(Hasher hasher) {
        this.hasher = hasher;
    }

    int hash(Invoke invoke, CSMethod[] nodes, int n) {
        return hasher.hash(invoke, nodes, n);
    }

    /**
     * @return the hub of the key, or null
     */
    @Nullable
    CallHub find(Invoke invoke, CSMethod[] nodes, int n, int hash) {
        int mask = slots.length - 1;
        for (int i = spread(hash) & mask; ; i = (i + 1) & mask) {
            CallHub hub = slots[i];
            if (hub == null) {
                return null;
            }
            if (hub.hash() == hash && hub.sameKey(invoke, nodes, n)) {
                return hub;
            }
        }
    }

    /**
     * Adds a hub whose key is not in the table.
     */
    void add(CallHub hub) {
        if (2 * (size + 1) > slots.length) {
            CallHub[] old = slots;
            slots = new CallHub[old.length * 2];
            for (CallHub h : old) {
                if (h != null) {
                    place(h);
                }
            }
        }
        place(hub);
        ++size;
    }

    private void place(CallHub hub) {
        int mask = slots.length - 1;
        int i = spread(hub.hash()) & mask;
        while (slots[i] != null) {
            i = (i + 1) & mask;
        }
        slots[i] = hub;
    }

    int size() {
        return size;
    }

    private static int spread(int h) {
        return h ^ (h >>> 16);
    }
}
