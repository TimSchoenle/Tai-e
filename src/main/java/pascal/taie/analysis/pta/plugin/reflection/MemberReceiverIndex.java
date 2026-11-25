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

package pascal.taie.analysis.pta.plugin.reflection;

import pascal.taie.language.classes.JClass;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * Pairs the instance members (the targets of {@code Method.invoke}, the
 * fields of {@code Field.get} and {@code Field.set}) and the receiver
 * objects of one reflective call site in one context, as both sets grow.
 * <p>
 * The JVM accepts a receiver for an instance member of class {@code C} only
 * when it is an instance of {@code C} (else {@code IllegalArgumentException}),
 * so only such pairs are visited. Members are kept by declaring class,
 * receivers by type, and receiver types by each class in their
 * {@link SupertypeClosure}. A new receiver visits only the members declared
 * in a supertype of its type; a new member visits only the receiver types
 * that are subtypes of its declaring class. Each (member, receiver) pair is
 * thus visited once, when the later of the two arrives, and the work of an
 * add is the number of objects given, the supertype closures of their
 * types, and the pairs it creates: linear in the delta, never the product
 * of both full sets.
 * <p>
 * A pair is visited by type: {@link PairAction#apply} gets the member, one
 * receiver type and the receivers of that type that are new to the pair.
 * The action must not add to this index. Members and receivers are kept in
 * insertion order, so that the order of the visits, which decides the
 * targets kept under {@code ReflectionAnalysis.ignoreImpreciseTarget},
 * does not depend on identity hash codes.
 * <p>
 * Within one handler call, add the new receivers before the new members:
 * the new receivers then meet the old members, and the new members meet
 * all receivers, so every new pair is visited exactly once.
 *
 * @param <M> the type of the members
 * @param <R> the type of the receivers
 */
final class MemberReceiverIndex<M, R> {

    /**
     * Handles new (member, receiver) pairs, by receiver type.
     */
    @FunctionalInterface
    interface PairAction<M, R> {

        /**
         * @param member       a member declared in a supertype of {@code receiverType}
         * @param receiverType the type of every receiver in {@code receivers}
         * @param receivers    the receivers not paired with {@code member} before
         */
        void apply(M member, Type receiverType, Collection<R> receivers);
    }

    private final SupertypeClosure supertypes;

    private final Function<? super M, JClass> declaringClassOf;

    private final Function<? super R, Type> typeOf;

    private final Map<JClass, Set<M>> membersByClass = Maps.newHybridMap();

    private final Map<Type, Set<R>> receiversByType = Maps.newHybridMap();

    /**
     * The receiver types present, by each class of their supertype closure.
     */
    private final Map<JClass, List<Type>> typesBySupertype = Maps.newHybridMap();

    /**
     * Objects given, supertype closure entries walked and (member, receiver
     * type) visits, so that a test can check that the work is linear in the
     * delta. Kept in production on purpose: one increment beside a map
     * probe per unit.
     */
    private long work;

    MemberReceiverIndex(SupertypeClosure supertypes,
                        Function<? super M, JClass> declaringClassOf,
                        Function<? super R, Type> typeOf) {
        this.supertypes = supertypes;
        this.declaringClassOf = declaringClassOf;
        this.typeOf = typeOf;
    }

    /**
     * Adds receivers and visits each new one with every known member that
     * is declared in a supertype of the receiver's type. Receivers already
     * present are skipped.
     */
    void addReceivers(Iterable<R> receivers, PairAction<M, R> action) {
        if (receivers instanceof Collection<?> collection && collection.isEmpty()) {
            return;
        }
        Map<Type, List<R>> added = Maps.newLinkedHashMap();
        for (R receiver : receivers) {
            ++work;
            Type type = typeOf.apply(receiver);
            Set<R> known = receiversByType.get(type);
            if (known == null) {
                known = Sets.newHybridOrderedSet();
                receiversByType.put(type, known);
                for (JClass supertype : supertypes.of(type)) {
                    ++work;
                    typesBySupertype.computeIfAbsent(supertype, k -> new ArrayList<>())
                            .add(type);
                }
            }
            if (known.add(receiver)) {
                added.computeIfAbsent(type, k -> new ArrayList<>()).add(receiver);
            }
        }
        added.forEach((type, newReceivers) -> {
            for (JClass supertype : supertypes.of(type)) {
                ++work;
                Set<M> members = membersByClass.get(supertype);
                if (members != null) {
                    for (M member : members) {
                        ++work;
                        action.apply(member, type, newReceivers);
                    }
                }
            }
        });
    }

    /**
     * Adds a member and, if it is new, visits it with every known receiver
     * whose type is a subtype of the member's declaring class.
     */
    void addMember(M member, PairAction<M, R> action) {
        ++work;
        JClass declaringClass = declaringClassOf.apply(member);
        if (membersByClass.computeIfAbsent(declaringClass, k -> Sets.newHybridOrderedSet())
                .add(member)) {
            List<Type> types = typesBySupertype.get(declaringClass);
            if (types != null) {
                for (Type type : types) {
                    ++work;
                    action.apply(member, type, receiversByType.get(type));
                }
            }
        }
    }

    /**
     * @return the objects given to this index plus the pairs it visited.
     */
    long work() {
        return work;
    }
}
