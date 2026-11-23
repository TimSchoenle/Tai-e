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
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.DeclaredParamProvider;
import pascal.taie.language.type.ArrayType;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A parameter whose class is missing from the class path is not known to be
 * abstract, so {@link DeclaredParamProvider} keeps a mock object for it
 * instead of failing.
 */
class MissingParamTypeTest {

    @Test
    void missingParamClassKeepsMockObjects() {
        MissingParamTypePlugin.provider = null;
        MissingParamTypePlugin.missingType = null;
        Main.main("-cp", "src/test/resources/pta/entrypoint",
                "--input-classes", "CustomEntryPoints",
                "-a", "pta=only-app:true;implicit-entries:false;"
                        + "plugins:[pascal.taie.analysis.pta.MissingParamTypePlugin];");
        DeclaredParamProvider provider = MissingParamTypePlugin.provider;
        assertNotNull(provider, "the plugin built no provider");
        assertNull(MissingParamTypePlugin.missingType.getJClass(),
                "the parameter class must be missing from the class path");

        Set<Obj> plain = provider.getParamObjs(0);
        assertEquals(1, plain.size(), "mock object of the missing class");
        Obj plainObj = plain.iterator().next();
        assertEquals(MissingParamTypePlugin.missingType, plainObj.getType());
        assertTrue(provider.getFieldObjs().get(plainObj).isEmpty(),
                "a missing class declares no known fields");

        Set<Obj> array = provider.getParamObjs(1);
        assertEquals(1, array.size(), "mock array of the missing class");
        Obj arrayObj = array.iterator().next();
        assertTrue(arrayObj.getType() instanceof ArrayType);
        Set<Obj> elems = provider.getArrayObjs().get(arrayObj);
        assertEquals(1, elems.size(), "mock element of the missing class");
        assertEquals(MissingParamTypePlugin.missingType, elems.iterator().next().getType());
    }
}
