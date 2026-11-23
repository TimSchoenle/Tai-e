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
import org.junit.jupiter.api.function.Executable;
import org.junit.jupiter.api.io.TempDir;
import pascal.taie.Main;
import pascal.taie.World;
import pascal.taie.analysis.pta.core.heap.MergedObj;
import pascal.taie.analysis.pta.core.heap.NewObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.ConfigException;

import java.io.File;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Option merge-library-objects: objects allocated in classes outside the
 * application class path are merged by type, the allocation sites of the
 * classes on it stay distinct.
 */
public class MergeLibraryObjectsTest {

    private static final String APP = "src/test/resources/pta/libheap/app";

    private static final String LIB = "src/test/resources/pta/libheap/lib";

    private static final String LIB_FIRST = "<LibHeapLib: java.lang.Object first()>";

    private static final String LIB_SECOND = "<LibHeapLib: java.lang.Object second()>";

    private static final String LIB_OTHER = "<LibHeapLib: java.lang.Object other()>";

    private static final String APP_FIRST = "<LibHeapApp: java.lang.Object first()>";

    private static final String APP_SECOND = "<LibHeapApp: java.lang.Object second()>";

    private static final Set<String> FIXTURE_CLASSES = Set.of(
            "LibHeapApp", "LibHeapApp$Nested", "LibHeapApp$1", "Item", "LibHeapLib", "Box");

    private static final String NESTED_FIRST = "<LibHeapApp$Nested: java.lang.Object first()>";

    private static final String NESTED_SECOND = "<LibHeapApp$Nested: java.lang.Object second()>";

    private static final String ANONYMOUS_GET = "<LibHeapApp$1: java.lang.Object get()>";

    @Test
    void offKeepsEveryAllocationSite() {
        run(false);
        Obj libFirst = onlyObj(LIB_FIRST);
        Obj libSecond = onlyObj(LIB_SECOND);
        assertInstanceOf(NewObj.class, libFirst);
        assertInstanceOf(NewObj.class, libSecond);
        assertNotEquals(libFirst, libSecond);
        assertNotEquals(onlyObj(APP_FIRST), onlyObj(APP_SECOND));
    }

    @Test
    void onMergesLibrarySitesOfOneType() {
        run(true);
        Obj libFirst = onlyObj(LIB_FIRST);
        assertInstanceOf(MergedObj.class, libFirst);
        assertEquals("Box", libFirst.getType().getName());
        assertEquals(libFirst, onlyObj(LIB_SECOND));
    }

    @Test
    void onKeepsLibrarySitesOfOtherTypesApart() {
        run(true);
        Obj other = onlyObj(LIB_OTHER);
        assertInstanceOf(MergedObj.class, other);
        assertNotEquals(onlyObj(LIB_FIRST), other);
    }

    @Test
    void onKeepsApplicationSites() {
        run(true);
        Obj appFirst = onlyObj(APP_FIRST);
        Obj appSecond = onlyObj(APP_SECOND);
        assertInstanceOf(NewObj.class, appFirst);
        assertInstanceOf(NewObj.class, appSecond);
        assertNotEquals(appFirst, appSecond);
    }

    @Test
    void onKeepsSitesOfNestedAndAnonymousApplicationClasses() {
        run(true);
        Obj nestedFirst = onlyObj(NESTED_FIRST);
        Obj nestedSecond = onlyObj(NESTED_SECOND);
        assertInstanceOf(NewObj.class, nestedFirst);
        assertInstanceOf(NewObj.class, nestedSecond);
        assertNotEquals(nestedFirst, nestedSecond);
        assertInstanceOf(NewObj.class, onlyObj(ANONYMOUS_GET));
    }

    @Test
    void offIsTheDefault() {
        Main.main("-acp", APP, "-cp", LIB, "-m", "LibHeapApp", "-a", "pta=");
        List<String> absent = snapshot();
        run(false);
        assertEquals(absent, snapshot());
    }

    @Test
    void onRefusesAnEmptyApplicationClassPath() {
        assertRefused("application class path", () -> Main.main(
                "-cp", APP + File.pathSeparator + LIB,
                "-m", "LibHeapApp",
                "-a", "pta=merge-library-objects:true;"));
    }

    @Test
    void onRefusesAnApplicationClassPathWithoutClasses(@TempDir Path empty) {
        assertRefused("application class path", () -> Main.main(
                "-acp", empty.toString(), "-cp", APP + File.pathSeparator + LIB,
                "-m", "LibHeapApp",
                "-a", "pta=merge-library-objects:true;"));
    }

    private static void assertRefused(String named, Executable analysis) {
        Throwable thrown = assertThrows(RuntimeException.class, analysis);
        while (thrown != null && !(thrown instanceof ConfigException
                && String.valueOf(thrown.getMessage()).contains(named))) {
            thrown = thrown.getCause();
        }
        assertNotNull(thrown, "no configuration failure naming " + named);
    }

    private static void run(boolean merge) {
        Main.main("-acp", APP, "-cp", LIB,
                "-m", "LibHeapApp",
                "-a", "pta=merge-library-objects:" + merge + ";");
    }

    /**
     * The number of objects of the run, and the points-to set of every
     * variable of the test's own classes.
     */
    private static List<String> snapshot() {
        PointerAnalysisResult pta = World.get().getResult(PointerAnalysis.ID);
        List<String> lines = new ArrayList<>();
        lines.add("objects " + pta.getObjects().size());
        pta.getVars().stream()
                .filter(v -> FIXTURE_CLASSES.contains(
                        v.getMethod().getDeclaringClass().getName()))
                .forEach(v -> lines.add(v.getMethod() + "/" + v.getName() + " "
                        + pta.getPointsToSet(v).stream().map(Obj::toString).sorted().toList()));
        Collections.sort(lines);
        return lines;
    }

    private static Obj onlyObj(String method) {
        PointerAnalysisResult pta = World.get().getResult(PointerAnalysis.ID);
        Set<Obj> objs = pta.getPointsToSet(World.get().getClassHierarchy()
                .getMethod(method).getIR().getReturnVars().get(0));
        assertEquals(1, objs.size(), "objects returned by " + method + ": " + objs);
        return objs.iterator().next();
    }
}
