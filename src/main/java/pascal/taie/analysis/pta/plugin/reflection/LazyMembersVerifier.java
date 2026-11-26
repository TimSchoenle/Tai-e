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

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.util.CSObjs;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassMember;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.Consumer;

/**
 * In-run check of lazy reflection members (px/s115-P52), enabled by
 * {@code -Dpx.lazymembers.verify=true}. At the end of the analysis it
 * recomputes, for every placeholder, the receiver classes and names its call
 * site saw from the points-to sets of the call's receiver and name argument,
 * and from them the members the eager objects of the lazily taken classes
 * would be, and checks:
 * <ul>
 * <li>the call site took every receiver class, each either eagerly or
 * lazily, the first N eagerly, and every name;</li>
 * <li>the placeholder holds exactly those members, and is handed out once it
 * has any;</li>
 * <li>every consumer call site ({@code Method.invoke}, {@code Field.get},
 * {@code Field.set}, {@code Constructor.newInstance},
 * {@code Method.getDeclaringClass}, {@code Method.getParameterAnnotations})
 * whose receiver points to the placeholder subscribed to it once, and every
 * subscription received every member of it exactly once, so the consumer
 * resolved what it resolves for the eager objects.</li>
 * </ul>
 * A difference throws {@link IllegalStateException} with the counts and the
 * first offenders. An analysis stopped by its time limit ends with work left,
 * so it is not checked.
 */
final class LazyMembersVerifier {

    private static final String ENABLED = "px.lazymembers.verify";

    /**
     * How many offenders of each kind a failure names.
     */
    private static final int SHOWN = 5;

    /**
     * The consumers of member objects, by callee signature, each with
     * whether it takes its member objects only when the call has a result.
     * Each takes them from its receiver.
     */
    private static final Map<String, Boolean> CONSUMERS = Map.of(
            "<java.lang.reflect.Method: java.lang.Object invoke(java.lang.Object,java.lang.Object[])>", false,
            "<java.lang.reflect.Field: java.lang.Object get(java.lang.Object)>", true,
            "<java.lang.reflect.Field: void set(java.lang.Object,java.lang.Object)>", false,
            "<java.lang.reflect.Constructor: java.lang.Object newInstance(java.lang.Object[])>", false,
            "<java.lang.reflect.Method: java.lang.Class getDeclaringClass()>", false,
            "<java.lang.reflect.Method: java.lang.annotation.Annotation[][] getParameterAnnotations()>", true);

    private final Solver solver;

    private final CSManager csManager;

    private final Set<Invoke> invokesWithLog;

    private final Map<SubscriptionKey, Subscription> subscriptions = new HashMap<>();

    private final List<SubscriptionKey> repeatedSubscriptions = new ArrayList<>();

    LazyMembersVerifier(Solver solver, Set<Invoke> invokesWithLog) {
        this.solver = solver;
        this.csManager = solver.getCSManager();
        this.invokesWithLog = invokesWithLog;
    }

    static boolean isEnabled() {
        return Boolean.getBoolean(ENABLED);
    }

    /**
     * Records the subscription of consumer call site {@code consumer} in
     * {@code context} to {@code summary}.
     *
     * @return the listener to register in place of {@code listener}: it
     * records every member it receives and passes it on
     */
    Consumer<ClassMember> track(MemberSummary summary, Context context, Invoke consumer,
                                Consumer<? super ClassMember> listener) {
        SubscriptionKey key = new SubscriptionKey(consumer, context, summary);
        Subscription subscription = new Subscription(new HashSet<>(), new ArrayList<>());
        if (subscriptions.putIfAbsent(key, subscription) != null) {
            repeatedSubscriptions.add(key);
        }
        return member -> {
            if (!subscription.received().add(member)) {
                subscription.repeated().add(member);
            }
            listener.accept(member);
        };
    }

    /**
     * Checks every summary of {@code summaries} and every consumer call site.
     *
     * @throws IllegalStateException on any difference
     */
    void verify(Collection<MemberSummary> summaries) {
        if (solver.isStoppedByTimeLimit()) {
            System.err.println("[refl] lazy members not verified: the analysis stopped"
                    + " at its time limit");
            return;
        }
        Failures failures = new Failures();
        long members = 0;
        for (MemberSummary summary : summaries) {
            checkProducer(summary, failures);
            members += summary.members().size();
        }
        checkSubscriptions(failures);
        long consumerSites = checkConsumerSites(failures);
        failures.throwIfAny();
        System.err.printf("[refl] lazy members verified: placeholders=%d members=%d"
                        + " subscriptions=%d consumer_receivers=%d%n",
                summaries.size(), members, subscriptions.size(), consumerSites);
    }

    private void checkProducer(MemberSummary summary, Failures failures) {
        Invoke invoke = summary.invoke();
        Context context = summary.context();
        Set<JClass> seen = new LinkedHashSet<>();
        pointsTo(context, ((InvokeInstanceExp) invoke.getInvokeExp()).getBase())
                .forEach(obj -> {
                    JClass clazz = CSObjs.toClass(obj);
                    if (clazz != null) {
                        seen.add(clazz);
                    }
                });
        Set<JClass> eager = summary.eagerClasses();
        Set<JClass> lazy = summary.classes();
        Set<JClass> taken = new HashSet<>(eager);
        taken.addAll(lazy);
        if (taken.size() != eager.size() + lazy.size()) {
            failures.add("producer", summary + " took a class both eagerly and lazily");
        }
        if (!taken.equals(seen)) {
            Set<JClass> missing = new LinkedHashSet<>(seen);
            missing.removeAll(taken);
            failures.add("producer", summary + " took " + taken.size() + " classes, its receiver holds "
                    + seen.size() + ", missing " + firstOf(missing));
        }
        if (eager.size() > summary.threshold()
                || (!lazy.isEmpty() && eager.size() < summary.threshold())) {
            failures.add("producer", summary + " took " + eager.size()
                    + " classes eagerly, threshold " + summary.threshold());
        }
        Set<String> names = new LinkedHashSet<>();
        if (summary.isNamed()) {
            pointsTo(context, invoke.getInvokeExp().getArg(0)).forEach(obj -> {
                String name = CSObjs.toString(obj);
                if (name != null) {
                    names.add(name);
                }
            });
            if (!summary.names().equals(names)) {
                failures.add("producer", summary + " took names " + firstOf(summary.names())
                        + ", its name argument holds " + firstOf(names));
            }
        }
        Set<ClassMember> expected = new LinkedHashSet<>();
        for (JClass clazz : lazy) {
            if (summary.isNamed()) {
                names.forEach(name ->
                        summary.source().members(clazz, name).forEach(expected::add));
            } else {
                summary.source().members(clazz, null).forEach(expected::add);
            }
        }
        Set<ClassMember> held = new HashSet<>(summary.members());
        if (held.size() != summary.members().size() || !held.equals(expected)) {
            Set<ClassMember> missing = new LinkedHashSet<>(expected);
            missing.removeAll(held);
            failures.add("producer", summary + " holds " + summary.members().size()
                    + " members, expected " + expected.size() + ", missing " + firstOf(missing));
        }
        if (summary.isPublished() == held.isEmpty()) {
            failures.add("producer", summary + " handed out=" + summary.isPublished()
                    + " with " + held.size() + " members");
        }
    }

    private void checkSubscriptions(Failures failures) {
        Map<MemberSummary, Set<ClassMember>> memberSets = new HashMap<>();
        subscriptions.forEach((key, subscription) -> {
            Set<ClassMember> expected = memberSets.computeIfAbsent(key.summary(),
                    summary -> new HashSet<>(summary.members()));
            if (!subscription.received().equals(expected)) {
                Set<ClassMember> missing = new LinkedHashSet<>(expected);
                missing.removeAll(subscription.received());
                failures.add("subscription", key + " received "
                        + subscription.received().size() + " of " + expected.size()
                        + " members, missing " + firstOf(missing));
            }
            if (!subscription.repeated().isEmpty()) {
                failures.add("subscription", key + " received again "
                        + firstOf(subscription.repeated()));
            }
        });
        repeatedSubscriptions.forEach(key ->
                failures.add("subscription", key + " subscribed again"));
    }

    /**
     * Checks that every reachable consumer call site subscribed to every
     * placeholder its receiver points to.
     *
     * @return the number of (consumer call site, placeholder) pairs checked
     */
    private long checkConsumerSites(Failures failures) {
        long sites = 0;
        for (CSMethod csMethod : solver.getCallGraph().reachableMethods().toList()) {
            Context context = csMethod.getContext();
            for (Invoke invoke : csMethod.getMethod().getIR().invokes(false).toList()) {
                JMethod callee = invoke.getMethodRef().resolveNullable();
                Boolean needsResult = callee == null ? null : CONSUMERS.get(callee.getSignature());
                if (needsResult == null || invokesWithLog.contains(invoke)
                        || (needsResult && invoke.getResult() == null)) {
                    continue;
                }
                Var base = ((InvokeInstanceExp) invoke.getInvokeExp()).getBase();
                for (CSObj obj : pointsTo(context, base)) {
                    if (obj.getObject().getAllocation() instanceof MemberSummary summary) {
                        ++sites;
                        if (!subscriptions.containsKey(
                                new SubscriptionKey(invoke, context, summary))) {
                            failures.add("consumer", invoke + " in " + context
                                    + " never subscribed to " + summary);
                        }
                    }
                }
            }
        }
        return sites;
    }

    /**
     * The points-to set of {@code var} in {@code context}, read without
     * creating its pointer, so that the check leaves the result as it is.
     */
    private Set<CSObj> pointsTo(Context context, Var var) {
        for (CSVar csVar : csManager.getCSVarsOf(var)) {
            if (csVar.getContext().equals(context)) {
                return csVar.getObjects();
            }
        }
        return Set.of();
    }

    private static String firstOf(Collection<?> items) {
        return items.stream().limit(SHOWN).toList()
                + (items.size() > SHOWN ? " and " + (items.size() - SHOWN) + " more" : "");
    }

    private record SubscriptionKey(Invoke consumer, Context context, MemberSummary summary) {

        @Override
        public String toString() {
            return consumer + " in " + context + " -> " + summary;
        }
    }

    private record Subscription(Set<ClassMember> received, List<ClassMember> repeated) {
    }

    /**
     * The failures, counted by kind, with the first offenders of each kind.
     */
    private static final class Failures {

        private final Map<String, Integer> counts = new TreeMap<>();

        private final List<String> shown = new ArrayList<>();

        void add(String kind, String offender) {
            int count = counts.merge(kind, 1, Integer::sum);
            if (count <= SHOWN) {
                shown.add(kind + ": " + offender);
            }
        }

        void throwIfAny() {
            if (!counts.isEmpty()) {
                throw new IllegalStateException("[refl] lazy members verification failed "
                        + counts + "; first offenders:\n  " + String.join("\n  ", shown));
            }
        }
    }
}
