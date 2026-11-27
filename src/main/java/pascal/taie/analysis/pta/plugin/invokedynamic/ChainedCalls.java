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

package pascal.taie.analysis.pta.plugin.invokedynamic;

import pascal.taie.analysis.pta.core.cs.element.CSCallSite;

/**
 * A set of pairs (call site, source) compared by identity, in two parallel
 * open-addressing arrays without a pair object or a hash node per element.
 * Identity equals {@link Object#equals} for the pairs of
 * {@link LambdaAnalysis}: a {@link CSCallSite} has identity equality, and
 * the sources are interned ({@link ChainedSources}). Elements are never
 * removed; there is no iteration.
 */
final class ChainedCalls {

    private static final int INITIAL_CAPACITY = 16;

    private CSCallSite[] sites = new CSCallSite[INITIAL_CAPACITY];

    private LambdaSource[] sources = new LambdaSource[INITIAL_CAPACITY];

    private int size;

    /**
     * Adds the pair {@code (csCallSite, source)}.
     *
     * @return whether the set did not contain the pair
     */
    boolean add(CSCallSite csCallSite, LambdaSource source) {
        CSCallSite[] s = sites;
        LambdaSource[] src = sources;
        int slot = findSlot(s, src, csCallSite, source);
        if (s[slot] != null) {
            return false;
        }
        if ((size + 1) * 3L > s.length * 2L) {
            int capacity = s.length * 2;
            CSCallSite[] newSites = new CSCallSite[capacity];
            LambdaSource[] newSources = new LambdaSource[capacity];
            for (int i = 0; i < s.length; ++i) {
                if (s[i] != null) {
                    int to = findSlot(newSites, newSources, s[i], src[i]);
                    newSites[to] = s[i];
                    newSources[to] = src[i];
                }
            }
            s = newSites;
            src = newSources;
            sites = s;
            sources = src;
            slot = findSlot(s, src, csCallSite, source);
        }
        s[slot] = csCallSite;
        src[slot] = source;
        ++size;
        return true;
    }

    /**
     * @return whether the set contains the pair {@code (csCallSite, source)}
     */
    boolean contains(CSCallSite csCallSite, LambdaSource source) {
        return sites[findSlot(sites, sources, csCallSite, source)] != null;
    }

    int size() {
        return size;
    }

    /**
     * Drops every pair and shrinks the arrays to their initial capacity.
     */
    void clear() {
        sites = new CSCallSite[INITIAL_CAPACITY];
        sources = new LambdaSource[INITIAL_CAPACITY];
        size = 0;
    }

    /**
     * @return the slot of the pair, or the empty slot where it belongs.
     */
    private static int findSlot(CSCallSite[] s, LambdaSource[] src,
                                CSCallSite csCallSite, LambdaSource source) {
        int mask = s.length - 1;
        int h = 31 * System.identityHashCode(csCallSite) + System.identityHashCode(source);
        int slot = (h ^ (h >>> 16)) & mask;
        CSCallSite site;
        while ((site = s[slot]) != null) {
            if (site == csCallSite && src[slot] == source) {
                return slot;
            }
            slot = (slot + 1) & mask;
        }
        return slot;
    }
}
