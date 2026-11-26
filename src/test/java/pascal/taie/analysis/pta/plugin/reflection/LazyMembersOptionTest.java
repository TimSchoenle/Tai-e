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

package pascal.taie.analysis.pta.plugin.reflection;

import org.junit.jupiter.api.Test;
import pascal.taie.config.ConfigException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The checks of option {@code reflection-members-lazy}
 * ({@link ReflectionAnalysis#lazyThreshold}). Android mode is tested here, as
 * a whole analysis in Android mode needs an Android program.
 */
class LazyMembersOptionTest {

    private static final String STRING_CONSTANT = "string-constant";

    @Test
    void offIsAlwaysAccepted() {
        assertEquals(-1, ReflectionAnalysis.lazyThreshold(-1, null, false, true));
    }

    @Test
    void aThresholdIsAccepted() {
        assertEquals(0, ReflectionAnalysis.lazyThreshold(0, STRING_CONSTANT, true, false));
        assertEquals(100, ReflectionAnalysis.lazyThreshold(100, STRING_CONSTANT, true, false));
    }

    @Test
    void androidModeIsRefused() {
        ConfigException thrown = assertThrows(ConfigException.class,
                () -> ReflectionAnalysis.lazyThreshold(0, STRING_CONSTANT, true, true));
        assertTrue(thrown.getMessage().contains("Android mode"), thrown::getMessage);
    }

    @Test
    void aThresholdBelowMinusOneIsRefused() {
        ConfigException thrown = assertThrows(ConfigException.class,
                () -> ReflectionAnalysis.lazyThreshold(-2, STRING_CONSTANT, true, false));
        assertTrue(thrown.getMessage().contains("-1 or at least 0"), thrown::getMessage);
    }

    @Test
    void otherInferencesAndNoMembersAreRefused() {
        assertThrows(ConfigException.class,
                () -> ReflectionAnalysis.lazyThreshold(0, "solar", true, false));
        assertThrows(ConfigException.class,
                () -> ReflectionAnalysis.lazyThreshold(0, STRING_CONSTANT, false, false));
    }
}
