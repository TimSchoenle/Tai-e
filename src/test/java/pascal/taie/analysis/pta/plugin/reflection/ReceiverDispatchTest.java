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
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Checks that {@link ReceiverDispatch} asks the class hierarchy once per
 * receiver type and answers every receiver with the hierarchy's own result,
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
        AtomicInteger calls = new AtomicInteger();
        JMethod target = method(hierarchy, "C", "bar");
        MethodRef bar = target.getRef();
        ReceiverDispatch dispatch = new ReceiverDispatch(counting(hierarchy, calls), target);
        Type d = hierarchy.getClass("D").getType();
        JMethod expected = hierarchy.dispatch(d, bar);
        assertNotNull(expected);
        for (int i = 0; i < RECEIVERS; i++) {
            assertEquals(expected, dispatch.dispatch(d));
        }
        assertEquals(1, calls.get());
    }

    @Test
    void eachReceiverTypeDispatchesOnce() {
        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        AtomicInteger calls = new AtomicInteger();
        JMethod target = method(hierarchy, "C", "foo");
        MethodRef foo = target.getRef();
        ReceiverDispatch dispatch = new ReceiverDispatch(counting(hierarchy, calls), target);
        Type c = hierarchy.getClass("C").getType();
        Type d = hierarchy.getClass("D").getType();
        Type[] receivers = {d, c, d, c, d};
        for (Type receiver : receivers) {
            assertEquals(hierarchy.dispatch(receiver, foo), dispatch.dispatch(receiver));
        }
        assertEquals(2, calls.get());
    }

    @Test
    void anUndispatchableTypeIsAskedOnce() {
        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        AtomicInteger calls = new AtomicInteger();
        JMethod target = method(hierarchy, "C", "bar");
        MethodRef bar = target.getRef();
        ReceiverDispatch dispatch = new ReceiverDispatch(counting(hierarchy, calls), target);
        Type i = hierarchy.getClass("I").getType();
        assertNull(hierarchy.dispatch(i, bar));
        for (int k = 0; k < RECEIVERS; k++) {
            assertNull(dispatch.dispatch(i));
        }
        assertEquals(1, calls.get());
    }

    @Test
    void anEarlierTypeWithoutCalleeIsFoundByOneLookup() {
        ClassHierarchy hierarchy = World.get().getClassHierarchy();
        JMethod target = method(hierarchy, "C", "bar");
        ReceiverDispatch dispatch = new ReceiverDispatch(undispatchable(), target);
        AtomicInteger hashes = new AtomicInteger();
        Type a = hashCounting(hashes);
        Type b = hashCounting(new AtomicInteger());
        assertNull(dispatch.dispatch(a));
        assertNull(dispatch.dispatch(b));
        hashes.set(0);
        assertNull(dispatch.dispatch(a));
        assertEquals(1, hashes.get());
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

    private static JMethod method(ClassHierarchy hierarchy, String className, String name) {
        JClass jclass = hierarchy.getClass(className);
        assertNotNull(jclass, className);
        JMethod method = jclass.getDeclaredMethod(name);
        assertNotNull(method, className + "." + name);
        return method;
    }

    /**
     * @return a class hierarchy that answers like {@code hierarchy} and
     * counts its {@code dispatch} calls in {@code calls}.
     */
    private static ClassHierarchy counting(ClassHierarchy hierarchy, AtomicInteger calls) {
        return (ClassHierarchy) Proxy.newProxyInstance(
                ClassHierarchy.class.getClassLoader(),
                new Class<?>[]{ClassHierarchy.class},
                (proxy, m, args) -> {
                    if ("dispatch".equals(m.getName())) {
                        calls.incrementAndGet();
                    }
                    try {
                        return m.invoke(hierarchy, args);
                    } catch (InvocationTargetException e) {
                        throw e.getCause();
                    }
                });
    }
}
