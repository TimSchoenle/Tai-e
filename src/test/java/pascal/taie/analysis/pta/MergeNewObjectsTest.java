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

import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.pta.core.heap.MergedObj;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.NewObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.ConfigException;
import pascal.taie.ir.exp.Var;
import pascal.taie.language.classes.JMethod;

import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Option {@code merge-new-objects} merges the objects of all allocation
 * sites of one type into one object, while objects that do not come from
 * an allocation site, such as lambda objects, stay per site.
 */
public class MergeNewObjectsTest {

    @Test
    void mergesAllocationSitesOfOneTypeButKeepsLambdasPerSite() {
        runTypeHeap(true);

        Obj b1 = onlyObj("b1");
        Obj b2 = onlyObj("b2");
        assertInstanceOf(MergedObj.class, b1);
        assertEquals(b1, b2);
        Obj c1 = onlyObj("c1");
        assertInstanceOf(MergedObj.class, c1);
        assertEquals(c1, onlyObj("c2"));

        Obj r1 = onlyObj("r1");
        Obj r2 = onlyObj("r2");
        assertInstanceOf(MockObj.class, r1);
        assertInstanceOf(MockObj.class, r2);
        assertNotEquals(r1, r2);
    }

    @Test
    void keepsEveryDispatchTargetOfMergedReceivers() {
        runTypeHeap(true);

        JMethod main = World.get().getClassHierarchy()
                .getMethod("<TypeHeap: void main(java.lang.String[])>");
        PointerAnalysisResult result = World.get().getResult(PointerAnalysis.ID);
        Set<String> callees = result.getCallGraph().getCalleesOfM(main).stream()
                .map(JMethod::getSignature)
                .collect(Collectors.toSet());
        assertTrue(callees.contains("<TypeHeap$Square: void draw()>"), callees::toString);
        assertTrue(callees.contains("<TypeHeap$Circle: void draw()>"), callees::toString);
    }

    @Test
    void keepsPrimitiveArraysAndZeroLengthArraysOutOfTheMerge() {
        runTypeHeap(true);

        Obj a1 = onlyObj("a1");
        assertInstanceOf(NewObj.class, a1);
        assertNotEquals(a1, onlyObj("a2"));
        assertInstanceOf(MockObj.class, onlyObj("z1"));
        // the dimensions array keeps its allocation site, so reflection
        // still resolves the rank of Array.newInstance(Class, int[])
        assertInstanceOf(MockObj.class, onlyObj("grid"));
    }

    @Test
    void refusesContextSensitivityAndAdvancedAnalyses() {
        for (String extra : new String[]{"cs:1-obj;", "advanced:zipper;"}) {
            Throwable thrown = assertThrows(RuntimeException.class,
                    () -> Main.main("-cp", "src/test/resources/pta/typeheap",
                            "-m", "TypeHeap",
                            "-a", "pta=merge-new-objects:true;" + extra));
            while (thrown != null && !(thrown instanceof ConfigException)) {
                thrown = thrown.getCause();
            }
            assertNotNull(thrown, extra);
        }
    }

    @Test
    void keepsOneObjectPerAllocationSiteByDefault() {
        runTypeHeap(false);

        Obj b1 = onlyObj("b1");
        assertInstanceOf(NewObj.class, b1);
        assertNotEquals(b1, onlyObj("b2"));
        assertNotEquals(onlyObj("a1"), onlyObj("a2"));
    }

    private static void runTypeHeap(boolean merge) {
        Main.main("-cp", "src/test/resources/pta/typeheap",
                "-m", "TypeHeap",
                "-a", "pta=handle-invokedynamic:true;"
                        + "merge-new-objects:" + merge + ";");
    }

    private static Obj onlyObj(String varName) {
        JMethod main = World.get().getClassHierarchy()
                .getMethod("<TypeHeap: void main(java.lang.String[])>");
        Var var = main.getIR().getVars().stream()
                .filter(v -> v.getName().equals(varName))
                .findFirst()
                .orElseThrow();
        PointerAnalysisResult result = World.get().getResult(PointerAnalysis.ID);
        Set<Obj> pts = result.getPointsToSet(var);
        assertEquals(1, pts.size(), () -> varName + " points to " + pts);
        return pts.iterator().next();
    }
}
