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
import pascal.taie.frontend.java.classes.DefaultClassLoader;
import pascal.taie.frontend.java.classes.PhantomClassBuilder;
import pascal.taie.frontend.java.classes.PhantomClassSource;
import pascal.taie.ir.exp.ClassLiteral;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.InvokeDynamic;
import pascal.taie.ir.exp.Literal;
import pascal.taie.ir.exp.MethodType;
import pascal.taie.language.annotation.AnnotationHolder;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.ClassNames;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JClassLoader;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Modifier;
import pascal.taie.language.classes.Signatures;
import pascal.taie.language.classes.Subsignature;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;

import java.lang.invoke.LambdaMetafactory;
import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The classes of the lambda objects that {@code LambdaMetafactory.altMetafactory}
 * creates with added interfaces. The class that the run time spins for such a
 * call implements the functional interface (the return type of the
 * invokedynamic), {@code java.io.Serializable} if the flags have
 * {@code FLAG_SERIALIZABLE} and each marker interface of {@code FLAG_MARKERS};
 * it declares the interface method (the name of the invokedynamic with the
 * descriptor of the first static argument) and each bridge of
 * {@code FLAG_BRIDGES}. Typed by the functional interface alone, such a lambda
 * object would be dropped by every type filter of an added interface (a cast,
 * an array store, a typed parameter, result or field), although the run time
 * accepts it, and a call through a default method of an added interface would
 * have no target.
 * <p>
 * Such a lambda object is typed by a synthetic final class that implements the
 * same interfaces and declares the same methods, abstract. The class hierarchy
 * then answers subtyping as the run time does and dispatches a default method
 * of an added interface, but no declared method: its lookup ends at an abstract
 * method of a final class, so a call of the interface method or of a bridge
 * stays unresolved and {@link LambdaAnalysis#onUnresolvedCall} connects it to
 * the implementation, as for a lambda object of {@code metafactory}. One class
 * serves every call with the same functional interface, added interfaces and
 * declared methods; it is added to the class hierarchy at its first use and
 * reused by later analyses of the same world.
 * <p>
 * A call that adds no interface, whose static arguments are not of the
 * documented kinds, or whose functional or added interface is missing or not
 * an interface (its linkage fails at run time) keeps the return type of the
 * invokedynamic as the type of its lambda object.
 */
final class LambdaClasses {

    /**
     * Index of the flags among the static arguments of {@code altMetafactory},
     * after the interface method type, the implementation and the
     * instantiated method type.
     */
    private static final int FLAGS_INDEX = 3;

    private static final String NAME_PREFIX = "pascal.taie.lambda.Lambda$";

    private final ClassHierarchy hierarchy;

    private final TypeSystem typeSystem;

    /**
     * The class type of each synthetic class name used so far.
     */
    private final Map<String, ClassType> types = new HashMap<>();

    /**
     * Interfaces and declared methods of a synthetic class.
     *
     * @param interfaces the functional interface first, then the added ones
     * @param methodName the name of the interface method and the bridges
     * @param methods    the method types of the interface method and the bridges
     */
    private record Shape(List<ClassType> interfaces, String methodName,
                         List<MethodType> methods) {

        /**
         * @return the class name, which differs for different shapes: every
         * character but an ASCII letter or digit is escaped as {@code _}
         * and four hex digits, so the separators cannot occur in a part.
         */
        String className() {
            StringBuilder key = new StringBuilder();
            interfaces.forEach(i -> key.append(i.getName()).append(','));
            key.append(';').append(methodName);
            methods.forEach(m -> key.append(';').append(m));
            StringBuilder name = new StringBuilder(NAME_PREFIX);
            key.chars().forEach(c -> {
                if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
                        || (c >= '0' && c <= '9')) {
                    name.append((char) c);
                } else {
                    name.append('_').append(String.format("%04x", c));
                }
            });
            return name.toString();
        }
    }

    LambdaClasses(ClassHierarchy hierarchy, TypeSystem typeSystem) {
        this.hierarchy = hierarchy;
        this.typeSystem = typeSystem;
    }

    /**
     * @param indy a lambda meta factory call
     * @return the type of the lambda objects of {@code indy}: the synthetic
     * class of its added interfaces, or the return type of {@code indy}.
     */
    Type typeOf(InvokeDynamic indy) {
        Type returnType = indy.getMethodType().getReturnType();
        if (!isAltMetafactory(indy)
                || !(returnType instanceof ClassType functional)) {
            return returnType;
        }
        Shape shape = shapeOf(indy, functional);
        if (shape == null) {
            return returnType;
        }
        return types.computeIfAbsent(shape.className(), name -> getOrCreate(shape, name));
    }

    /**
     * @return the number of synthetic class types used so far.
     */
    int size() {
        return types.size();
    }

    private static boolean isAltMetafactory(InvokeDynamic indy) {
        JMethod bsm = indy.getBootstrapMethodRef().resolveNullable();
        return bsm != null && bsm.getSignature().equals(Signatures.LAMBDA_ALTMETAFACTORY);
    }

    /**
     * @return the shape of the class of {@code indy}'s lambda objects, or
     * null if it adds no interface or cannot link (see the class comment).
     */
    private @Nullable Shape shapeOf(InvokeDynamic indy, ClassType functional) {
        List<Literal> args = indy.getBootstrapArgs();
        if (args.size() <= FLAGS_INDEX
                || !(args.get(0) instanceof MethodType interfaceMethod)
                || !(args.get(FLAGS_INDEX) instanceof IntLiteral flagsLiteral)) {
            return null;
        }
        int flags = flagsLiteral.getValue();
        Set<ClassType> interfaces = new LinkedHashSet<>();
        interfaces.add(functional);
        if ((flags & LambdaMetafactory.FLAG_SERIALIZABLE) != 0) {
            interfaces.add(typeSystem.getClassType(ClassNames.SERIALIZABLE));
        }
        int next = FLAGS_INDEX + 1;
        if ((flags & LambdaMetafactory.FLAG_MARKERS) != 0) {
            int count = countAt(args, next);
            if (count < 0) {
                return null;
            }
            for (int i = next + 1; i <= next + count; ++i) {
                if (!(args.get(i) instanceof ClassLiteral marker
                        && marker.getTypeValue() instanceof ClassType markerType)) {
                    return null;
                }
                interfaces.add(markerType);
            }
            next += 1 + count;
        }
        List<MethodType> methods = new ArrayList<>();
        methods.add(interfaceMethod);
        if ((flags & LambdaMetafactory.FLAG_BRIDGES) != 0) {
            int count = countAt(args, next);
            if (count < 0) {
                return null;
            }
            for (int i = next + 1; i <= next + count; ++i) {
                if (!(args.get(i) instanceof MethodType bridge)) {
                    return null;
                }
                methods.add(bridge);
            }
        }
        if (interfaces.size() == 1) {
            return null;
        }
        for (ClassType i : interfaces) {
            JClass jclass = i.getJClass();
            if (jclass == null || jclass.isPhantom() || !jclass.isInterface()) {
                return null;
            }
        }
        return new Shape(List.copyOf(interfaces), indy.getMethodName(), List.copyOf(methods));
    }

    /**
     * @return the count at {@code index} of {@code args} if it is an int
     * literal and that many arguments follow it, otherwise -1.
     */
    private static int countAt(List<Literal> args, int index) {
        if (index >= args.size() || !(args.get(index) instanceof IntLiteral countLiteral)) {
            return -1;
        }
        int count = countLiteral.getValue();
        return count >= 0 && index + count < args.size() ? count : -1;
    }

    private ClassType getOrCreate(Shape shape, String name) {
        return hierarchy.allClasses()
                .filter(c -> c.getName().equals(name))
                .map(JClass::getType)
                .findFirst()
                .orElseGet(() -> create(shape, name));
    }

    private ClassType create(Shape shape, String name) {
        PhantomClassSource source = new PhantomClassSource(name, false);
        JClassLoader loader = new DefaultClassLoader(List.of(source));
        JClass jclass = loader.loadClass(name);
        List<JClass> interfaces = shape.interfaces().stream()
                .map(ClassType::getJClass)
                .toList();
        Map<Subsignature, JMethod> methods = new LinkedHashMap<>();
        for (MethodType m : shape.methods()) {
            methods.computeIfAbsent(
                    Subsignature.get(shape.methodName(), m.getParamTypes(), m.getReturnType()),
                    s -> new JMethod(jclass, shape.methodName(),
                            EnumSet.of(Modifier.PUBLIC, Modifier.ABSTRACT),
                            m.getParamTypes(), m.getReturnType(), List.of(), null,
                            AnnotationHolder.emptyHolder(), null, null, null));
        }
        ClassType type = typeSystem.getClassType(loader, name);
        jclass.build(new PhantomClassBuilder(typeSystem, source) {

            @Override
            public Set<Modifier> getModifiers() {
                return EnumSet.of(Modifier.PUBLIC, Modifier.FINAL, Modifier.SYNTHETIC);
            }

            @Override
            public ClassType getClassType() {
                return type;
            }

            @Override
            public Collection<JClass> getInterfaces() {
                return interfaces;
            }

            @Override
            public Collection<JMethod> getDeclaredMethods() {
                return methods.values();
            }

            @Override
            public boolean isPhantom() {
                return false;
            }
        });
        hierarchy.addClass(jclass);
        return type;
    }
}
