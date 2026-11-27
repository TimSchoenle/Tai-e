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

import org.jspecify.annotations.Nullable;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.ir.exp.InvokeDynamic;

import java.util.List;
import java.util.Objects;

/**
 * The interned sources with arguments ({@link LambdaSource#getSamArgs}) of
 * {@link LambdaAnalysis}: at most one source per value of
 * {@link LambdaSource#equals}, held in one open-addressing table of the
 * sources themselves, without a key object or a hash node per source.
 * Elements are never removed; there is no iteration.
 */
final class ChainedSources {

    private static final int INITIAL_CAPACITY = 16;

    private LambdaSource[] table = new LambdaSource[INITIAL_CAPACITY];

    private int size;

    /**
     * @return the interned source equal to
     * {@code new LambdaSource(indy, context, samArgs)}, created (with its own
     * copy of {@code samArgs}) if absent.
     */
    LambdaSource intern(InvokeDynamic indy, Context context, List<CSVar> samArgs) {
        LambdaSource[] tab = table;
        int slot = findSlot(tab, indy, context, samArgs);
        LambdaSource found = tab[slot];
        if (found != null) {
            return found;
        }
        LambdaSource source = new LambdaSource(indy, context, List.copyOf(samArgs));
        if ((size + 1) * 3L > tab.length * 2L) {
            tab = rehash(tab, tab.length * 2);
            table = tab;
            slot = findSlot(tab, indy, context, samArgs);
        }
        tab[slot] = source;
        ++size;
        return source;
    }

    /**
     * @return the interned source equal to
     * {@code new LambdaSource(indy, context, samArgs)}, or null if absent.
     */
    @Nullable
    LambdaSource find(InvokeDynamic indy, Context context, List<CSVar> samArgs) {
        LambdaSource[] tab = table;
        return tab[findSlot(tab, indy, context, samArgs)];
    }

    int size() {
        return size;
    }

    /**
     * Drops every source and shrinks the table to its initial capacity.
     */
    void clear() {
        table = new LambdaSource[INITIAL_CAPACITY];
        size = 0;
    }

    private static int hash(InvokeDynamic indy, Context context, List<CSVar> samArgs) {
        int h = 31 * (31 * indy.hashCode() + context.hashCode()) + samArgs.hashCode();
        return h ^ (h >>> 16);
    }

    /**
     * @return the slot of the source equal to (indy, context, samArgs), or
     * the empty slot where it belongs.
     */
    private static int findSlot(LambdaSource[] tab, InvokeDynamic indy, Context context,
                                List<CSVar> samArgs) {
        int mask = tab.length - 1;
        int slot = hash(indy, context, samArgs) & mask;
        LambdaSource s;
        while ((s = tab[slot]) != null) {
            if (s.getIndy().equals(indy) && s.getContext().equals(context)
                    && samArgs.equals(s.getSamArgs())) {
                return slot;
            }
            slot = (slot + 1) & mask;
        }
        return slot;
    }

    private static LambdaSource[] rehash(LambdaSource[] old, int capacity) {
        LambdaSource[] tab = new LambdaSource[capacity];
        for (LambdaSource s : old) {
            if (s != null) {
                List<CSVar> args = Objects.requireNonNull(s.getSamArgs(),
                        "a chained source without arguments");
                tab[findSlot(tab, s.getIndy(), s.getContext(), args)] = s;
            }
        }
        return tab;
    }
}
