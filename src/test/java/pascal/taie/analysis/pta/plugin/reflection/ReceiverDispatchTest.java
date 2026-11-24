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
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Proxy;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * Checks that {@link ReceiverDispatch} copies the receivers once, asks the
 * class hierarchy once per (target, receiver type) in the order of first
 * occurrence, and answers every receiver with the hierarchy's own result,
 * over the classes of {@code Hierarchy.java} ({@code D extends C}; the
 * interface {@code I} is no subclass of {@code C}).
 */
class ReceiverDispatchTest {

    private static final int RECEIVERS = 5;

    @BeforeAll
    static void buildWorld() {
        Main.buildWorld("-cp", "src/test/resources/world", "--input-classes", "Hierarchy");
    }

    @Test
    void receiversOfOneTypeDispatchOnce() {
        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        List<String> calls = new ArrayList<>();
        JMethod target = method(hierarchy, "C", "bar");
        Type d = type(hierarchy, "D");
        JMethod expected = hierarchy.dispatch(d, target.getRef());
        assertNotNull(expected);
        List<Type> receivers = new ArrayList<>();
        for (int i = 0; i < RECEIVERS; i++) {
            receivers.add(d);
        }
        ReceiverDispatch<Type> dispatch = dispatchOver(recording(hierarchy, calls), receivers);
        dispatch.startTarget(target);
        assertEquals(RECEIVERS, dispatch.size());
        for (int i = 0; i < RECEIVERS; i++) {
            assertSame(d, dispatch.receiver(i));
            assertEquals(expected, dispatch.dispatch(i));
        }
        assertEquals(List.of("D.bar"), calls);
    }

    @Test
    void anUndispatchableTypeIsAskedOnce() {
        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        List<String> calls = new ArrayList<>();
        JMethod target = method(hierarchy, "C", "bar");
        Type i = type(hierarchy, "I");
        assertNull(hierarchy.dispatch(i, target.getRef()));
        ReceiverDispatch<Type> dispatch = dispatchOver(
                recording(hierarchy, calls), List.of(i, i, i));
        dispatch.startTarget(target);
        for (int k = 0; k < dispatch.size(); k++) {
            assertNull(dispatch.dispatch(k));
        }
        assertEquals(List.of("I.bar"), calls);
    }

    @Test
    void targetsShareOneCopyAndDispatchEachTypeInFirstOccurrenceOrder() {
        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        List<String> calls = new ArrayList<>();
        Type c = type(hierarchy, "C");
        Type d = type(hierarchy, "D");
        Type i = type(hierarchy, "I");
        List<Type> receivers = List.of(d, c, d, i, c, i);
        AtomicInteger iterations = new AtomicInteger();
        AtomicInteger typeReads = new AtomicInteger();
        Iterable<Type> source = new Iterable<>() {
            @Override
            public Iterator<Type> iterator() {
                throw new UnsupportedOperationException("iterator");
            }

            @Override
            public void forEach(Consumer<? super Type> action) {
                iterations.incrementAndGet();
                receivers.forEach(action);
            }
        };
        ReceiverDispatch<Type> dispatch = new ReceiverDispatch<>(
                recording(hierarchy, calls), source, receivers.size(), t -> {
                    typeReads.incrementAndGet();
                    return t;
                });
        for (String name : List.of("foo", "bar")) {
            JMethod target = method(hierarchy, "C", name);
            MethodRef ref = target.getRef();
            dispatch.startTarget(target);
            assertEquals(receivers.size(), dispatch.size());
            for (int k = 0; k < dispatch.size(); k++) {
                assertSame(receivers.get(k), dispatch.receiver(k));
                assertEquals(hierarchy.dispatch(receivers.get(k), ref), dispatch.dispatch(k));
            }
        }
        assertEquals(List.of("D.foo", "C.foo", "I.foo", "D.bar", "C.bar", "I.bar"), calls);
        assertEquals(1, iterations.get());
        assertEquals(receivers.size(), typeReads.get());
    }

    @Test
    void dispatchProbesNoMapAfterTheCopy() {
        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        AtomicInteger hashes = new AtomicInteger();
        Type a = hashCounting(hashes);
        Type b = hashCounting(hashes);
        ReceiverDispatch<Type> dispatch = dispatchOver(undispatchable(), List.of(a, b, a, b));
        dispatch.startTarget(method(hierarchy, "C", "bar"));
        int afterCopy = hashes.get();
        for (int k = 0; k < dispatch.size(); k++) {
            assertNull(dispatch.dispatch(k));
        }
        dispatch.startTarget(method(hierarchy, "C", "foo"));
        for (int k = 0; k < dispatch.size(); k++) {
            assertNull(dispatch.dispatch(k));
        }
        assertEquals(afterCopy, hashes.get());
    }

    private static ReceiverDispatch<Type> dispatchOver(
            ClassHierarchy hierarchy, List<Type> receivers) {
        return new ReceiverDispatch<>(hierarchy, receivers, receivers.size(), t -> t);
    }

    private static Type type(ClassHierarchy hierarchy, String className) {
        JClass jclass = hierarchy.getClass(className);
        assertNotNull(jclass, className);
        return jclass.getType();
    }

    private static JMethod method(ClassHierarchy hierarchy, String className, String name) {
        JClass jclass = hierarchy.getClass(className);
        assertNotNull(jclass, className);
        JMethod method = jclass.getDeclaredMethod(name);
        assertNotNull(method, className + "." + name);
        return method;
    }

    /**
     * @return a class hierarchy that answers like {@code hierarchy} and
     * records each {@code dispatch} call in {@code calls} as
     * {@code type.method}.
     */
    private static ClassHierarchy recording(ClassHierarchy hierarchy, List<String> calls) {
        return (ClassHierarchy) Proxy.newProxyInstance(
                ClassHierarchy.class.getClassLoader(),
                new Class<?>[]{ClassHierarchy.class},
                (proxy, m, args) -> {
                    if ("dispatch".equals(m.getName())) {
                        calls.add(((Type) args[0]).getName() + "."
                                + ((MethodRef) args[1]).getName());
                    }
                    try {
                        return m.invoke(hierarchy, args);
                    } catch (InvocationTargetException e) {
                        throw e.getCause();
                    }
                });
    }

    /**
     * @return a class hierarchy whose {@code dispatch} answers {@code null}
     * for every type and that refuses every other call.
     */
    private static ClassHierarchy undispatchable() {
        return (ClassHierarchy) Proxy.newProxyInstance(
                ClassHierarchy.class.getClassLoader(),
                new Class<?>[]{ClassHierarchy.class},
                (proxy, m, args) -> {
                    if ("dispatch".equals(m.getName())) {
                        return null;
                    }
                    throw new UnsupportedOperationException(m.getName());
                });
    }

    /**
     * @return a type with identity equality that counts its {@code hashCode}
     * calls in {@code hashes}.
     */
    private static Type hashCounting(AtomicInteger hashes) {
        return (Type) Proxy.newProxyInstance(
                Type.class.getClassLoader(),
                new Class<?>[]{Type.class},
                (proxy, m, args) -> switch (m.getName()) {
                    case "hashCode" -> {
                        hashes.incrementAndGet();
                        yield System.identityHashCode(proxy);
                    }
                    case "equals" -> proxy == args[0];
                    case "toString" -> "CountingType@" + System.identityHashCode(proxy);
                    default -> throw new UnsupportedOperationException(m.getName());
                });
    }
}
