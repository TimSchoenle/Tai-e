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

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.TrieContext;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.TestElements;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.plugin.util.InvokeHandler;
import pascal.taie.analysis.pta.plugin.util.InvokeUtils;
import pascal.taie.ir.exp.ClassLiteral;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.StringLiteral;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JClass;

import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * {@link LazyMembersVerifier} on a hand-built summary of the
 * {@code getDeclaredMethod} call of fixture {@code LazyNamed}: it passes
 * when the consumer received every member, and fails with the kind of the
 * difference when a delivery was missed or a call outside its consumer
 * table subscribed. Its consumer table is the set of invoke handlers that
 * take member objects from their receiver.
 */
class LazyMembersVerifierTest {

    private static final Context EMPTY = new TrieContext.Factory<>().getEmptyContext();

    private static final MemberSummary.Source DECLARED_METHODS = (clazz, name) ->
            clazz.getDeclaredMethods().stream()
                    .filter(method -> name == null || method.getName().equals(name));

    private static Invoke getDeclaredMethod;

    private static Invoke methodInvoke;

    private static JClass lnA;

    @BeforeAll
    static void buildWorld() {
        Main.buildWorld("-cp", "src/test/resources/pta", "-cp", "src/test/resources/pta/reflsound",
                "-m", "LazyNamed");
        JClass main = World.get().getClassHierarchy().getClass("LazyNamed");
        List<Invoke> invokes = main.getDeclaredMethod("methods").getIR().invokes(false).toList();
        getDeclaredMethod = invokeOf(invokes, "getDeclaredMethod");
        methodInvoke = invokeOf(invokes, "invoke");
        lnA = World.get().getClassHierarchy().getClass("LnA");
    }

    @Test
    void passesWhenTheConsumerReceivedEveryMember() {
        LazyMembersVerifier verifier = verifier();
        MemberSummary summary = summaryWithMemberA(verifier);
        summary.subscribe(EMPTY, methodInvoke, member -> {
        });
        verifier.verify(List.of(summary));
    }

    @Test
    void aMissedDeliveryFailsAsASubscription() {
        LazyMembersVerifier verifier = verifier();
        MemberSummary summary = summaryWithMemberA(verifier);
        // recorded as a subscription, but never registered with the summary,
        // so it misses the member
        verifier.track(summary, EMPTY, methodInvoke, member -> {
        });
        IllegalStateException thrown = assertThrows(IllegalStateException.class,
                () -> verifier.verify(List.of(summary)));
        assertKinds("{subscription=1}", thrown);
    }

    @Test
    void aSubscriptionOutsideTheConsumerTableFails() {
        LazyMembersVerifier verifier = verifier();
        MemberSummary summary = summaryWithMemberA(verifier);
        summary.subscribe(EMPTY, getDeclaredMethod, member -> {
        });
        IllegalStateException thrown = assertThrows(IllegalStateException.class,
                () -> verifier.verify(List.of(summary)));
        assertKinds("{consumer-table=1}", thrown);
    }

    /**
     * The consumer table names exactly the handlers of the models that run
     * with lazy members (the solar and Android models are refused with
     * them) whose receiver is a member object: a handler of
     * {@code Method}, {@code Field} or {@code Constructor} that reads its
     * base.
     */
    @Test
    void theConsumerTableIsTheMemberReceiverHandlers() {
        Set<String> handlers = new TreeSet<>();
        Stream.of(ReflectiveActionModel.class, OthersModel.class, StringBasedModel.class)
                .flatMap(model -> Arrays.stream(model.getDeclaredMethods()))
                .forEach(method -> addMemberReceiverHandlers(method, handlers));
        assertEquals(handlers, new TreeSet<>(LazyMembersVerifier.consumers().keySet()));
    }

    private static void addMemberReceiverHandlers(Method method, Set<String> handlers) {
        for (InvokeHandler handler : method.getAnnotationsByType(InvokeHandler.class)) {
            if (Arrays.stream(handler.argIndexes()).noneMatch(i -> i == InvokeUtils.BASE)) {
                continue;
            }
            for (String signature : handler.signature()) {
                if (signature.startsWith("<java.lang.reflect.Method:")
                        || signature.startsWith("<java.lang.reflect.Field:")
                        || signature.startsWith("<java.lang.reflect.Constructor:")) {
                    handlers.add(signature);
                }
            }
        }
    }

    private static void assertKinds(String kinds, IllegalStateException thrown) {
        String message = thrown.getMessage();
        String counts = message.substring(message.indexOf('{'), message.indexOf('}') + 1);
        assertEquals(kinds, counts, message);
    }

    /**
     * @return a summary at threshold 0 that took class LnA and name "a", so
     * holds LnA.a(), and was handed out
     */
    private static MemberSummary summaryWithMemberA(LazyMembersVerifier verifier) {
        MemberSummary summary = new MemberSummary(getDeclaredMethod, EMPTY, DECLARED_METHODS,
                true, 0, s -> {
                    throw new AssertionError("the check makes no placeholder object");
                }, verifier);
        assertEquals(true, summary.isLazy(lnA));
        summary.addName("a");
        summary.addClass(lnA);
        assertEquals(1, summary.members().size(), summary.members()::toString);
        assertEquals(true, summary.publish());
        return summary;
    }

    /**
     * @return a check that reads the receiver of the
     * {@code getDeclaredMethod} call as holding LnA's class object, its name
     * argument as holding "a", and no reachable method
     */
    private static LazyMembersVerifier verifier() {
        Var base = ((InvokeInstanceExp) getDeclaredMethod.getInvokeExp()).getBase();
        Var name = getDeclaredMethod.getInvokeExp().getArg(0);
        CSObj classObj = TestElements.object(new MockObj(() -> "class", ClassLiteral.get(lnA.getType()),
                lnA.getType(), null, false), 0);
        CSObj nameObj = TestElements.object(new MockObj(() -> "name", StringLiteral.get("a"),
                lnA.getType(), null, false), 1);
        return new LazyMembersVerifier(new LazyMembersVerifier.AnalysisState() {
            @Override
            public boolean isStoppedByTimeLimit() {
                return false;
            }

            @Override
            public List<CSMethod> reachableMethods() {
                return List.of();
            }

            @Override
            public Set<CSObj> pointsTo(Context context, Var var) {
                if (var == base) {
                    return Set.of(classObj);
                }
                return var == name ? Set.of(nameObj) : Set.of();
            }
        }, Set.of());
    }

    private static Invoke invokeOf(List<Invoke> invokes, String name) {
        return invokes.stream()
                .filter(invoke -> invoke.getMethodRef().getName().equals(name))
                .findFirst().orElseThrow(() -> new AssertionError("no call of " + name));
    }
}
