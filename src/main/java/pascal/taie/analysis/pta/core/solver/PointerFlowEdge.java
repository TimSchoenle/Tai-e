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
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.util.Hashes;
import pascal.taie.util.collection.ArraySet;
import pascal.taie.util.collection.HybridHashSet;
import pascal.taie.util.graph.Edge;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Objects;
import java.util.Set;
import java.util.function.Consumer;

public class PointerFlowEdge implements Edge<Pointer> {

    private final FlowKind kind;

    private final Pointer source;

    private final Pointer target;

    /**
     * Number of transfers kept in {@link #first} and {@link #rest} as an
     * array; equal to the small-set size of {@link HybridHashSet}, so that
     * the iteration order of the transfers is the one of that set.
     */
    private static final int SMALL_LIMIT = new HybridHashSet<Transfer>().getThreshold();

    /**
     * The first transfer added to this edge, or null if none.
     */
    private @Nullable Transfer first;

    /**
     * Further transfers: null if at most one, a {@code Transfer[]} holding
     * the second and later ones in insertion order while there are at most
     * {@link #SMALL_LIMIT} in all, or a {@link HybridHashSet} holding all
     * of them once an addition reached it with the edge full (then
     * {@link #first} only marks the edge as non-empty).
     */
    private @Nullable Object rest;

    public PointerFlowEdge(FlowKind kind, Pointer source, Pointer target) {
        this.kind = kind;
        this.source = source;
        this.target = target;
    }

    public FlowKind kind() {
        return kind;
    }

    public Pointer source() {
        return source;
    }

    public Pointer target() {
        return target;
    }

    /**
     * @return String representation of information for this edge.
     * By default, the information represents the {@link FlowKind},
     * and other subclasses of {@link PointerFlowEdge} may contain
     * additional content.
     */
    public String getInfo() {
        return kind.name();
    }

    /**
     * Adds a transfer to this edge unless an equal transfer is already
     * there. The transfers keep the order of the {@link HybridHashSet} they
     * replace: insertion order while the edge holds at most
     * {@link #SMALL_LIMIT} transfers; once it holds that many, any further
     * addition (a duplicate included, as that set upgrades on it) moves
     * them into a {@link HybridHashSet} built by the same additions.
     *
     * @return true if the transfer was added.
     */
    public boolean addTransfer(Transfer transfer) {
        Objects.requireNonNull(transfer, "transfer");
        if (first == null) {
            first = transfer;
            return true;
        }
        if (rest instanceof Set<?> large) {
            @SuppressWarnings("unchecked")
            Set<Transfer> set = (Set<Transfer>) large;
            return set.add(transfer);
        }
        Transfer[] more = (Transfer[]) rest;
        int n = more == null ? 0 : more.length;
        if (n + 1 >= SMALL_LIMIT) {
            Set<Transfer> set = new HybridHashSet<>();
            set.add(first);
            if (more != null) {
                for (Transfer t : more) {
                    set.add(t);
                }
            }
            rest = set;
            return set.add(transfer);
        }
        if (first.equals(transfer)) {
            return false;
        }
        for (int i = 0; i < n; i++) {
            if (more[i].equals(transfer)) {
                return false;
            }
        }
        Transfer[] grown = more == null ? new Transfer[1] : Arrays.copyOf(more, n + 1);
        grown[n] = transfer;
        rest = grown;
        return true;
    }

    /**
     * Applies the action to each transfer of this edge, in the order of
     * {@link #getTransfers()}, without allocating a view.
     */
    public void forEachTransfer(Consumer<? super Transfer> action) {
        if (first == null) {
            return;
        }
        if (rest instanceof Set<?> large) {
            for (Object t : large) {
                action.accept((Transfer) t);
            }
            return;
        }
        action.accept(first);
        Transfer[] more = (Transfer[]) rest;
        if (more != null) {
            for (Transfer t : more) {
                action.accept(t);
            }
        }
    }

    /**
     * @return an unmodifiable snapshot of the transfers of this edge.
     */
    public Set<Transfer> getTransfers() {
        if (first == null) {
            return Set.of();
        }
        ArrayList<Transfer> all = new ArrayList<>();
        forEachTransfer(all::add);
        return Collections.unmodifiableSet(new ArraySet<>(all, true));
    }

    @Override
    public int hashCode() {
        return Hashes.hash(source, target);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        PointerFlowEdge that = (PointerFlowEdge) o;
        return source.equals(that.source) && target.equals(that.target);
    }

    @Override
    public String toString() {
        return "[" + getInfo() + "]" + source + " -> " + target;
    }
}
