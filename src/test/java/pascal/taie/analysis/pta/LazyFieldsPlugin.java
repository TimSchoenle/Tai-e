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

import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Var;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

/**
 * Models fixture {@code reflsound/LazyFields}: {@code LfSink.store(m, v)}
 * stores {@code v} into field {@code LfSink.cell} of every member object
 * of {@code m}, and {@code LfSink.load(m)} returns that field of every
 * member object of {@code m}, as JDK code stores into and loads from the
 * fields of {@code Method} objects (the method accessor cache).
 */
public class LazyFieldsPlugin implements Plugin {

    private static final String STORE = "<LfSink: void store(java.lang.reflect.Method,java.lang.Object)>";

    private static final String LOAD = "<LfSink: java.lang.Object load(java.lang.reflect.Method)>";

    private static final String CELL = "<LfSink: java.lang.Object cell>";

    private Solver solver;

    private CSManager csManager;

    @Override
    public void setSolver(Solver solver) {
        this.solver = solver;
        this.csManager = solver.getCSManager();
    }

    @Override
    public void onNewPointsToSet(CSVar csVar, PointsToSet pts) {
        Var var = csVar.getVar();
        JMethod method = var.getMethod();
        String signature = method.getSignature();
        boolean store = signature.equals(STORE);
        if (!(store || signature.equals(LOAD))) {
            return;
        }
        IR ir = method.getIR();
        if (!var.equals(ir.getParam(0))) {
            return;
        }
        Context context = csVar.getContext();
        JField cell = solver.getHierarchy().getField(CELL);
        for (CSObj obj : pts) {
            InstanceField field = csManager.getInstanceField(obj, cell);
            if (store) {
                solver.addPFGEdge(csManager.getCSVar(context, ir.getParam(1)), field,
                        FlowKind.INSTANCE_STORE);
            } else {
                solver.addPFGEdge(field, csManager.getCSVar(context, ir.getReturnVars().get(0)),
                        FlowKind.INSTANCE_LOAD);
            }
        }
    }
}
