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

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Catch;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An exception thrown in a method that is called over a lambda, a
 * reflective or a privileged-action call edge reaches the catch variable
 * around the call site, and a call on the caught object reaches the
 * override of the thrown type.
 */
public class ExceptionOverOtherEdgesTest {

    private static final String MAIN = "ExceptionOverOtherEdges";

    private static PointerAnalysisResult pta;

    private static ClassHierarchy hierarchy;

    @BeforeAll
    static void analyse() {
        Main.main("-cp", "src/test/resources/pta/exception",
                "-m", MAIN,
                "-a", "pta=cs:ci;implicit-entries:false;only-app:true;"
                        + "handle-invokedynamic:true");
        pta = World.get().getResult(PointerAnalysis.ID);
        hierarchy = World.get().getClassHierarchy();
    }

    @Test
    void exceptionThrownInLambdaBodyReachesTheCaller() {
        assertCaughtAndDispatched("throwInLambda", "LambdaFailure");
    }

    @Test
    void exceptionThrownInReflectiveCalleeReachesTheCaller() {
        assertCaughtAndDispatched("throwInReflectiveCallee", "ReflectiveFailure");
    }

    @Test
    void exceptionThrownInPrivilegedActionReachesTheCaller() {
        assertCaughtAndDispatched("throwInPrivilegedAction", "PrivilegedFailure");
    }

    private static void assertCaughtAndDispatched(String callerName, String thrownType) {
        JMethod caller = hierarchy.getMethod(
                "<" + MAIN + ": void " + callerName + "()>");
        List<Catch> catches = caller.getIR().stmts()
                .filter(Catch.class::isInstance)
                .map(Catch.class::cast)
                .toList();
        assertEquals(1, catches.size(), "catch statements of " + caller);
        Var caught = catches.get(0).getExceptionRef();
        assertTrue(pta.getPointsToSet(caught).stream()
                        .anyMatch(obj -> obj.getType().getName().equals(thrownType)),
                thrownType + " objects caught in " + caller);
        Invoke getMessage = caller.getIR().invokes(false)
                .filter(invoke -> invoke.getMethodRef().getName().equals("getMessage"))
                .findFirst()
                .orElseThrow();
        CallGraph<Invoke, JMethod> callGraph = pta.getCallGraph();
        Set<JMethod> targets = callGraph.getCalleesOf(getMessage);
        JMethod override = hierarchy.getMethod(
                "<" + thrownType + ": java.lang.String getMessage()>");
        assertTrue(targets.contains(override),
                "targets of " + getMessage + ": " + targets);
    }
}
