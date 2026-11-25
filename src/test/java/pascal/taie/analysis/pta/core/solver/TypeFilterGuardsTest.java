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

package pascal.taie.analysis.pta.core.solver;

import org.junit.jupiter.api.Test;
import pascal.taie.Main;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.language.type.TypeSystem;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The guard block of the type filters counts a guard whose memo knows no
 * object neither as passing nor as failing every known object.
 */
public class TypeFilterGuardsTest {

    @Test
    void guardThatKnowsNoObjectIsNeitherAllPassNorAllFail() {
        Probe.block = null;
        Main.main("-cp", "src/test/resources/pta/fan", "-m", "FanOut",
                "-a", "pta=only-app:true;implicit-entries:false;plugins:["
                        + Probe.class.getName() + "]");
        String block = Probe.block;
        assertTrue(block != null && block.startsWith("guards=1 all_pass=0 all_fail=0\n"),
                String.valueOf(block));
        assertTrue(block.endsWith(" known=0 pass=0 fail=0"), block);
    }

    /**
     * At onFinish, applies a new filter of a guard type that no other
     * filter uses to an empty set (its memo then knows no object), and
     * reads the guard block of that filter alone.
     */
    public static class Probe implements Plugin {

        static String block;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            TypeSystem types = solver.getTypeSystem();
            TypeFilter fresh = new TypeFilter(
                    types.getArrayType(types.getClassType("A"), 3), solver);
            fresh.apply(null, solver.makePointsToSet());
            block = TypeFilter.guardsBlock(List.of(fresh), true, 5);
        }
    }
}
