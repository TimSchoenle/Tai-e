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

package pascal.taie.analysis.pta.core.heap;

import pascal.taie.config.ConfigException;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.util.ClassNameExtractor;

import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

/**
 * Finds the classes that lie on the application class path ({@code -acp}),
 * read by {@link ClassNameExtractor} as the world builder reads that path,
 * together with their nested, local and anonymous classes.
 * <p>
 * This is not {@link JClass#isApplication()}: the Soot front end runs in
 * application mode, which marks every referenced class outside the JDK as an
 * application class, libraries on {@code -cp} included.
 * <p>
 * A source file on a directory entry stands for the class its file name
 * names; further top-level classes in that file are not found.
 */
final class AppClassPathClasses {

    private AppClassPathClasses() {
    }

    /**
     * @param appClassPath the entries of the application class path
     * @param hierarchy    the classes of the analysed world
     * @return the classes of the world whose top-level class is on the path,
     * as a set by identity
     * @throws ConfigException if the path holds no class
     */
    static Set<JClass> of(List<String> appClassPath, ClassHierarchy hierarchy) {
        Set<String> names = new HashSet<>();
        for (String path : appClassPath) {
            // the world builder has read the same entries the same way
            names.addAll(ClassNameExtractor.extract(path));
        }
        if (names.isEmpty()) {
            throw new ConfigException("no class on the application class path "
                    + appClassPath + " to keep allocation sites for");
        }
        Set<JClass> classes = Collections.newSetFromMap(new IdentityHashMap<>());
        hierarchy.allClasses()
                .filter(c -> names.contains(topLevel(c).getName()))
                .forEach(classes::add);
        return classes;
    }

    private static JClass topLevel(JClass c) {
        JClass top = c;
        while (top.getOuterClass() != null) {
            top = top.getOuterClass();
        }
        return top;
    }
}
