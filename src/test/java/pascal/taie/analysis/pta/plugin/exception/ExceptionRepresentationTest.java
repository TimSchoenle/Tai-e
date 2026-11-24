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

package pascal.taie.analysis.pta.plugin.exception;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import pascal.taie.World;
import pascal.taie.analysis.Tests;
import pascal.taie.analysis.pta.PointerAnalysis;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.ir.stmt.Catch;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.IndexerBitSet;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Numbering exception objects by the exception analysis' own indexer gives
 * the same points-to sets (catch variables included) and the same call
 * graph as numbering them by the global indexer.
 */
public class ExceptionRepresentationTest {

    private static final String DIR = "exception";

    @ParameterizedTest
    @CsvSource({
            "ExceptionCircle,",
            "ExceptionCircleAndRecursion,",
            "ExceptionNoneCaught,",
            "ExceptionTreeAndRecursion,",
            "ExceptionFromClinit,cs:1-call",
            "CatchDispatch,",
    })
    void localNumberingSolvesLikeGlobalNumbering(String main, String cs) {
        String[] local = options(cs, Recorder.class);
        Tests.testPTA(false, DIR, main, local);
        List<String> localPointsTo = Recorder.pointsTo;
        List<String> localCatchPointsTo = Recorder.catchPointsTo;
        List<String> localEdges = Recorder.edges;
        Tests.testPTA(false, DIR, main, options(cs, GlobalNumberingRecorder.class));
        assertEquals(Recorder.pointsTo, localPointsTo);
        assertEquals(Recorder.catchPointsTo, localCatchPointsTo);
        assertEquals(Recorder.edges, localEdges);
        assertFalse(localEdges.isEmpty(), "no call edge recorded");
    }

    @Test
    void callOnCaughtObjectReachesTheThrownTypesOverride() {
        Tests.testPTA(false, DIR, "CatchDispatch", options(null, Recorder.class));
        assertFalse(Recorder.catchPointsTo.isEmpty(), "no catch variable recorded");
        PointerAnalysisResult pta = World.get().getResult(PointerAnalysis.ID);
        JMethod main = World.get().getMainMethod();
        Invoke describe = main.getIR().invokes(false)
                .filter(invoke -> invoke.getMethodRef().getName().equals("describe"))
                .findFirst()
                .orElseThrow();
        Set<String> callees = pta.getCallGraph().getCalleesOf(describe).stream()
                .map(JMethod::getSignature)
                .collect(Collectors.toSet());
        assertEquals(Set.of("<CatchDispatchSub: void describe()>"), callees);
    }

    private static String[] options(String cs, Class<? extends Plugin> recorder) {
        String plugins = "plugins:[" + recorder.getName() + "]";
        return cs == null ? new String[]{plugins} : new String[]{cs, plugins};
    }

    /**
     * Records every points-to set of a variable, those of catch variables
     * apart, and every call edge, as sorted text.
     */
    public static class Recorder implements Plugin {

        static List<String> pointsTo;

        static List<String> catchPointsTo;

        static List<String> edges;

        Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            CSManager csManager = solver.getCSManager();
            pointsTo = csManager.getCSVars().stream()
                    .map(Recorder::describe)
                    .sorted()
                    .toList();
            catchPointsTo = csManager.getCSVars().stream()
                    .filter(Recorder::isCatchVar)
                    .map(Recorder::describe)
                    .sorted()
                    .toList();
            edges = solver.getCallGraph().edges()
                    .map(edge -> edge.getKind() + " " + edge.getCallSite() + " -> "
                            + edge.getCallee())
                    .sorted()
                    .toList();
        }

        private static boolean isCatchVar(CSVar csVar) {
            return !csVar.getObjects().isEmpty()
                    && csVar.getVar().getMethod().getIR().stmts()
                    .anyMatch(stmt -> stmt instanceof Catch c
                            && c.getExceptionRef() == csVar.getVar());
        }

        private static String describe(CSVar csVar) {
            return csVar + " -> " + csVar.getObjects().stream()
                    .map(Object::toString)
                    .sorted()
                    .toList();
        }
    }

    /**
     * Records like {@link Recorder}, with the exception sets numbered by the
     * global {@link pascal.taie.analysis.pta.core.cs.element.CSObj} indexer.
     */
    public static class GlobalNumberingRecorder extends Recorder {

        @Override
        public void onStart() {
            CSManager csManager = solver.getCSManager();
            ExceptionAnalysisAccess.replaceSetFactory(solver,
                    () -> new IndexerBitSet<>(csManager.getObjectIndexer(), false));
        }
    }
}
