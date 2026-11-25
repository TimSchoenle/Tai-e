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

import pascal.taie.util.Copyable;

import java.util.Collection;
import java.util.Set;

/**
 * This interface extends {@link Set} to provide more useful APIs.
 *
 * @param <E> type of elements in this set
 */
public interface SetEx<E> extends Set<E>, Copyable<SetEx<E>> {

    /**
     * Adds all elements in collection {@code c}, and returns the difference set
     * between {@code c} and this set (before the call).
     *
     * @return a set of elements that are contained in {@code c} but
     * not in this set before the call.
     */
    SetEx<E> addAllDiff(Collection<? extends E> c);

    /**
     * Same as {@link #addAllDiff(Collection)}, but may reuse {@code diff}
     * for the result instead of allocating a new set. Either way
     * {@code diff} must no longer be used except through the returned set.
     *
     * @param c    the elements to add
     * @param diff a set that may be cleared and overwritten; neither this
     *             set nor {@code c}
     * @return a set of elements that are contained in {@code c} but
     * not in this set before the call: {@code diff} or a new set.
     */
    default SetEx<E> addAllDiff(Collection<? extends E> c, SetEx<E> diff) {
        return addAllDiff(c);
    }

    /**
     * @return {@code true} if this set has at least one element
     * contained in the given set.
     */
    boolean hasOverlapWith(Set<E> other);
}
