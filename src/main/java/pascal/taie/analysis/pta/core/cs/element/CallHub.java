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
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.ir.stmt.Invoke;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicLong;

/**
 * A call hub (option {@code call-hubs}, px/s116 re-keyed B): the plain call
 * edges from every member call site of one invoke to one fixed set of callee
 * nodes, stored once. The pair (member, target) is a call edge for each
 * member and each target; {@link CSCallSite} and {@link CSMethod} expand
 * their hubs in their edge views. The targets never change; members are
 * appended. A member's targets are announced one by one while the solver
 * joins it ({@link #beginJoin}, {@link #announce}, {@link #endJoin}): until
 * a target is announced, the views do not show that member's edge to it, so
 * every callback sees the edges a solve without hubs would have added so far.
 * <p>
 * The solver's relay pointers of the hub ({@link #argRelay}, {@link
 * #retRelay}) carry the union of the members' arguments to the targets'
 * parameters and the union of the targets' returns to the members' results.
 */
public final class CallHub {

    /** Above this many targets, positions are looked up in an index table. */
    private static final int LINEAR_MAX = 8;

    /**
     * Bumped by every join and every announcement of any hub; caches over
     * the expanded edges are valid only for one value.
     */
    private static final AtomicLong STAMP = new AtomicLong();

    private final Invoke invoke;

    private final CSMethod[] targets;

    private final int hash;

    /** Per slot a target's position + 1, 0 if free; null when linear. */
    private final int @Nullable [] index;

    private CSCallSite[] members = new CSCallSite[2];

    private int memberCount;

    private @Nullable CSCallSite joining;

    private int joiningVisible;

    private MockPointer @Nullable [] argRelays;

    private @Nullable MockPointer retRelay;

    private boolean relaysSet;

    /**
     * The allocation key of a relay pointer of a hub; {@code position} is
     * the argument index, -1 for the return.
     */
    public record RelaySlot(CallHub hub, int position) {
    }

    private CallHub(Invoke invoke, CSMethod[] targets, int hash) {
        this.invoke = invoke;
        this.targets = targets;
        this.hash = hash;
        this.index = targets.length > LINEAR_MAX ? buildIndex(targets) : null;
    }

    /**
     * Makes a hub and registers it as a hub of each of its targets; its
     * relay pointers follow by {@link #setRelays}.
     *
     * @param targets the callee nodes, distinct, at least two; the hub keeps
     *                the array
     * @param hash    {@link #hashOf} of the invoke and the targets
     */
    public static CallHub create(Invoke invoke, CSMethod[] targets, int hash) {
        if (targets.length < 2) {
            throw new IllegalArgumentException("a call hub needs two targets: " + targets.length);
        }
        CallHub hub = new CallHub(invoke, targets, hash);
        for (CSMethod target : targets) {
            target.addHub(hub);
        }
        return hub;
    }

    /**
     * Sets the relay pointers, once, before the first member joins.
     *
     * @param argRelays per argument index its relay pointer or null; null
     *                  if no argument is relayed
     * @param retRelay  the return relay pointer, or null
     */
    public void setRelays(MockPointer @Nullable [] argRelays, @Nullable MockPointer retRelay) {
        if (relaysSet || memberCount != 0) {
            throw new IllegalStateException("relays of a hub of " + invoke + " set twice or late");
        }
        relaysSet = true;
        this.argRelays = argRelays;
        this.retRelay = retRelay;
    }

    /**
     * @return the order-independent hash of a node set at an invoke
     */
    public static int hashOf(Invoke invoke, CSMethod[] nodes, int size) {
        int h = 0;
        for (int i = 0; i < size; ++i) {
            h += mix(System.identityHashCode(nodes[i]));
        }
        return 31 * invoke.hashCode() + h;
    }

    private static int mix(int h) {
        h *= 0x9E3779B9;
        return h ^ (h >>> 16);
    }

    private static int[] buildIndex(CSMethod[] targets) {
        int capacity = Integer.highestOneBit(targets.length * 2 - 1) << 1;
        int[] table = new int[capacity];
        int mask = capacity - 1;
        for (int i = 0; i < targets.length; ++i) {
            int slot = mix(System.identityHashCode(targets[i])) & mask;
            while (table[slot] != 0) {
                slot = (slot + 1) & mask;
            }
            table[slot] = i + 1;
        }
        return table;
    }

    public Invoke getInvoke() {
        return invoke;
    }

    public int hash() {
        return hash;
    }

    public int targetCount() {
        return targets.length;
    }

    public CSMethod target(int i) {
        return targets[i];
    }

    /**
     * @return the position of {@code node} among the targets, or -1
     */
    public int indexOf(CSMethod node) {
        int[] table = index;
        if (table == null) {
            for (int i = 0; i < targets.length; ++i) {
                if (targets[i] == node) {
                    return i;
                }
            }
            return -1;
        }
        int mask = table.length - 1;
        int slot = mix(System.identityHashCode(node)) & mask;
        while (true) {
            int p = table[slot];
            if (p == 0) {
                return -1;
            }
            if (targets[p - 1] == node) {
                return p - 1;
            }
            slot = (slot + 1) & mask;
        }
    }

    public boolean contains(CSMethod node) {
        return indexOf(node) >= 0;
    }

    /**
     * @return whether this hub's invoke and targets equal {@code invoke}
     * and the first {@code size} of {@code nodes} (distinct) as a set
     */
    public boolean sameKey(Invoke invoke, CSMethod[] nodes, int size) {
        if (this.invoke != invoke || targets.length != size) {
            return false;
        }
        for (int i = 0; i < size; ++i) {
            if (!contains(nodes[i])) {
                return false;
            }
        }
        return true;
    }

    public int memberCount() {
        return memberCount;
    }

    public CSCallSite member(int i) {
        return members[i];
    }

    public @Nullable MockPointer argRelay(int i) {
        MockPointer[] relays = argRelays;
        return relays == null || i >= relays.length ? null : relays[i];
    }

    public @Nullable MockPointer retRelay() {
        return retRelay;
    }

    /**
     * Appends {@code site} as a member; none of its targets is announced
     * yet. The caller has made sure that the site is no member.
     */
    public void beginJoin(CSCallSite site) {
        if (joining != null) {
            throw new IllegalStateException("nested join of " + site + " into a hub of " + invoke);
        }
        if (memberCount == members.length) {
            members = Arrays.copyOf(members, memberCount + Math.max(2, memberCount >> 1));
        }
        members[memberCount++] = site;
        joining = site;
        joiningVisible = 0;
        site.addHub(this);
        STAMP.incrementAndGet();
    }

    /**
     * Announces the next target of the joining member.
     */
    public void announce() {
        if (joining == null || joiningVisible >= targets.length) {
            throw new IllegalStateException("no target left to announce at " + invoke);
        }
        ++joiningVisible;
        STAMP.incrementAndGet();
    }

    /**
     * Ends the join: every target of the member is announced.
     */
    public void endJoin() {
        joining = null;
        joiningVisible = 0;
        STAMP.incrementAndGet();
    }

    /**
     * @return how many targets the views show for member {@code site}
     */
    int visibleTargets(CSCallSite site) {
        return joining == site ? joiningVisible : targets.length;
    }

    /**
     * @return how many members the views show for target {@code target}:
     * all but a joining member to which the target is not announced yet
     */
    int visibleMembers(CSMethod target) {
        return joining != null && indexOf(target) >= joiningVisible
                ? memberCount - 1 : memberCount;
    }

    /**
     * @return the current stamp of all hubs
     */
    static long stamp() {
        return STAMP.get();
    }

    /**
     * @return the plain edge from {@code site} to target {@code i}
     */
    Edge<CSCallSite, CSMethod> edge(CSCallSite site, int i) {
        return site.plainEdgeTo(targets[i]);
    }

    @Override
    public String toString() {
        return "CallHub{" + invoke + ", targets=" + targets.length
                + ", members=" + memberCount + '}';
    }
}
