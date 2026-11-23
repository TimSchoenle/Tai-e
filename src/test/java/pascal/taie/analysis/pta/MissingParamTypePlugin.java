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

package pascal.taie.analysis.pta;

import pascal.taie.analysis.pta.core.solver.DeclaredParamProvider;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.language.annotation.AnnotationHolder;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Modifier;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.language.type.VoidType;

import java.util.List;
import java.util.Set;

/**
 * Builds a {@link DeclaredParamProvider} (k = 1) for an entry method whose
 * parameter types name a class that is not on the class path, and keeps it
 * for {@link MissingParamTypeTest}.
 */
public class MissingParamTypePlugin implements Plugin {

    static final String MISSING_CLASS = "MissingParamType";

    static volatile DeclaredParamProvider provider;

    static volatile ClassType missingType;

    private Solver solver;

    @Override
    public void setSolver(Solver solver) {
        this.solver = solver;
    }

    @Override
    public void onStart() {
        JClass clz = solver.getHierarchy().getClass("CustomEntryPoints");
        TypeSystem typeSystem = solver.getTypeSystem();
        ClassType missing = typeSystem.getClassType(MISSING_CLASS);
        List<Type> params = List.of(missing, typeSystem.getArrayType(missing, 1));
        JMethod method = new JMethod(clz, "entryWithMissingParam",
                Set.of(Modifier.PUBLIC, Modifier.STATIC), params, VoidType.VOID,
                List.of(), null, AnnotationHolder.emptyHolder(), null, null, new Object());
        missingType = missing;
        provider = new DeclaredParamProvider(method, solver.getHeapModel(), 1);
    }
}
