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

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

class IdentityScratchMapTest {

    @Test
    void keysAreComparedByIdentityAndKeptInFirstPutOrder() {
        IdentityScratchMap map = new IdentityScratchMap();
        String a = new String("k");
        String b = new String("k");
        Object va = new Object();
        Object vb = new Object();
        map.put(a, va);
        map.put(b, vb);
        assertSame(va, map.get(a));
        assertSame(vb, map.get(b));
        assertNull(map.get("k"));
        assertEquals(2, map.size());
        assertSame(a, map.keyAt(0));
        assertSame(b, map.keyAt(1));
        assertThrows(IndexOutOfBoundsException.class, () -> map.keyAt(2));
        assertThrows(IllegalStateException.class, () -> map.put(a, vb));
    }

    @Test
    void growsKeepingEveryValueAndTheOrder() {
        IdentityScratchMap map = new IdentityScratchMap();
        List<Object> keys = new ArrayList<>();
        for (int i = 0; i < 1000; ++i) {
            Object key = new Object();
            keys.add(key);
            map.put(key, i);
        }
        assertEquals(1000, map.size());
        for (int i = 0; i < 1000; ++i) {
            assertEquals(i, map.get(keys.get(i)));
            assertSame(keys.get(i), map.keyAt(i));
        }
    }

    @Test
    void clearRemovesEveryKeyAndAllowsReuse() {
        IdentityScratchMap map = new IdentityScratchMap();
        Object[] keys = new Object[40];
        for (int i = 0; i < keys.length; ++i) {
            keys[i] = new Object();
            map.put(keys[i], i);
        }
        map.clear();
        assertEquals(0, map.size());
        for (Object key : keys) {
            assertNull(map.get(key));
        }
        map.put(keys[3], "again");
        assertEquals("again", map.get(keys[3]));
        assertSame(keys[3], map.keyAt(0));
    }

    @Test
    void refusesNullKeysAndValues() {
        IdentityScratchMap map = new IdentityScratchMap();
        assertThrows(NullPointerException.class, () -> map.put(null, "v"));
        assertThrows(NullPointerException.class, () -> map.put(new Object(), null));
        assertEquals(0, map.size());
    }
}
