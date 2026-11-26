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

import org.jspecify.annotations.Nullable;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassMember;
import pascal.taie.language.classes.JClass;
import pascal.taie.util.collection.Sets;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Stream;

/**
 * The members of one lazy member placeholder (option
 * {@code reflection-members-lazy}, px/s115-P52): the members that one
 * member-retrieving call site returns in one call context for the receiver
 * classes taken lazily, and for the getters with a name argument the names
 * seen there. This object is the allocation of the placeholder
 * {@link Obj}, so every holder of the placeholder reaches its members.
 * <p>
 * The member set only grows. Each member is delivered once: to every
 * listener registered at that time, and to every later listener when it
 * registers ({@link #subscribe}). The placeholder object itself never
 * changes, so growth never repropagates a points-to set; it reaches the
 * consumers only through their listeners.
 * <p>
 * Equality is identity: {@link LazyMembers} makes one summary per
 * (call site, call context). The hash code is computed from texts (the
 * signature of the call site's container, its index and the context's text),
 * not from the identity hashes of the call site and the context, so a hash
 * order over summaries is the same in every run as far as the context's text
 * is. The placeholder object's own hash still includes the identity hash of
 * its descriptor, as every mock object's does.
 */
final class MemberSummary {

    /**
     * The members of one receiver class, of the given name, or of every name
     * when {@code name} is {@code null} (the getters without a name argument).
     */
    @FunctionalInterface
    interface Source {
        Stream<? extends ClassMember> members(JClass clazz, @Nullable String name);
    }

    private final Invoke invoke;

    private final Context context;

    private final Source source;

    /**
     * Whether the call has a name argument: then a member counts only for a
     * name in {@link #names}.
     */
    private final boolean named;

    /**
     * How many receiver classes the call site takes eagerly (concrete member
     * objects) before it takes them lazily.
     */
    private final int threshold;

    private final Set<JClass> eagerClasses = Sets.newHybridSet();

    private final Set<JClass> classes = Sets.newLinkedSet();

    private final Set<String> names = Sets.newLinkedSet();

    private final List<ClassMember> delivered = new ArrayList<>();

    private final Set<ClassMember> deliveredSet = Sets.newHybridSet();

    private final List<Consumer<? super ClassMember>> listeners = new ArrayList<>();

    /**
     * Makes the placeholder object, on first use only, so that a call site
     * that never takes a class lazily adds no heap object.
     */
    private final Function<MemberSummary, Obj> objMaker;

    /**
     * The in-run check that records every subscription, or {@code null}.
     */
    private final @Nullable LazyMembersVerifier verifier;

    private final int hashCode;

    private @Nullable Obj obj;

    private boolean published;

    MemberSummary(Invoke invoke, Context context, Source source,
                  boolean named, int threshold, Function<MemberSummary, Obj> objMaker,
                  @Nullable LazyMembersVerifier verifier) {
        this.invoke = invoke;
        this.context = context;
        this.source = source;
        this.named = named;
        this.threshold = threshold;
        this.objMaker = objMaker;
        this.verifier = verifier;
        this.hashCode = 31 * (31 * invoke.getContainer().getSignature().hashCode()
                + invoke.getIndex()) + context.toString().hashCode();
    }

    /**
     * @return the placeholder object whose allocation this summary is
     */
    Obj getObj() {
        Obj placeholder = obj;
        if (placeholder == null) {
            placeholder = Objects.requireNonNull(objMaker.apply(this));
            obj = placeholder;
        }
        return placeholder;
    }

    /**
     * Whether {@code clazz} is taken lazily. The first {@link #threshold}
     * distinct classes are taken eagerly and stay so; every later class is
     * taken lazily. Answers the same for the same class every time.
     */
    boolean isLazy(JClass clazz) {
        if (classes.contains(clazz)) {
            return true;
        }
        if (eagerClasses.contains(clazz)) {
            return false;
        }
        if (eagerClasses.size() < threshold) {
            eagerClasses.add(clazz);
            return false;
        }
        return true;
    }

    /**
     * Adds a receiver class taken lazily and delivers its new members.
     */
    void addClass(JClass clazz) {
        if (classes.add(clazz)) {
            if (named) {
                // a listener may add a name while the members are delivered
                for (String name : List.copyOf(names)) {
                    deliver(source.members(clazz, name));
                }
            } else {
                deliver(source.members(clazz, null));
            }
        }
    }

    /**
     * Adds a name of a call with a name argument and delivers the new
     * members of the classes taken so far.
     */
    void addName(String name) {
        if (!named) {
            throw new IllegalStateException("no name argument at " + this);
        }
        if (names.add(name)) {
            for (JClass clazz : List.copyOf(classes)) {
                deliver(source.members(clazz, name));
            }
        }
    }

    private void deliver(Stream<? extends ClassMember> members) {
        members.forEach(member -> {
            if (deliveredSet.add(member)) {
                delivered.add(member);
                // a listener registered while this member is delivered
                // received it in its replay
                int count = listeners.size();
                for (int i = 0; i < count; ++i) {
                    listeners.get(i).accept(member);
                }
            }
        });
    }

    /**
     * Hands every member delivered so far to {@code listener}, and every
     * later member when it is delivered.
     *
     * @param context  the context of the consumer call site
     * @param consumer the consumer call site
     */
    void subscribe(Context context, Invoke consumer, Consumer<? super ClassMember> listener) {
        Consumer<? super ClassMember> registered = verifier == null ? listener
                : verifier.track(this, context, consumer, listener);
        subscribe(registered);
    }

    private void subscribe(Consumer<? super ClassMember> listener) {
        int count = delivered.size();
        listeners.add(listener);
        for (int i = 0; i < count; ++i) {
            listener.accept(delivered.get(i));
        }
    }

    /**
     * Marks the placeholder as handed out, the first time it has a member:
     * an empty placeholder stays out of every points-to set, as no concrete
     * member object would be there.
     *
     * @return whether the caller hands out the placeholder now
     */
    boolean publish() {
        if (!published && !delivered.isEmpty()) {
            published = true;
            return true;
        }
        return false;
    }

    /**
     * @return the members delivered so far, in delivery order (a view)
     */
    List<ClassMember> members() {
        return Collections.unmodifiableList(delivered);
    }

    Invoke invoke() {
        return invoke;
    }

    Context context() {
        return context;
    }

    Source source() {
        return source;
    }

    boolean isNamed() {
        return named;
    }

    int threshold() {
        return threshold;
    }

    /**
     * @return the receiver classes taken eagerly (a view)
     */
    Set<JClass> eagerClasses() {
        return Collections.unmodifiableSet(eagerClasses);
    }

    /**
     * @return the receiver classes taken lazily (a view)
     */
    Set<JClass> classes() {
        return Collections.unmodifiableSet(classes);
    }

    /**
     * @return the names taken (a view)
     */
    Set<String> names() {
        return Collections.unmodifiableSet(names);
    }

    /**
     * @return whether the placeholder was handed out
     */
    boolean isPublished() {
        return published;
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public boolean equals(Object o) {
        return this == o;
    }

    /**
     * A deterministic text: the container, the index and the API of the call
     * site, and the call context.
     */
    @Override
    public String toString() {
        return "LazyMembers{" + invoke.getContainer() + "[" + invoke.getIndex() + "]."
                + invoke.getMethodRef().getName() + " in " + context + "}";
    }
}
