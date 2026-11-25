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
import pascal.taie.analysis.Tests;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Soundness of the string-constant reflection model: every target a
 * reflective call can run is a call edge (px/s115). The fixtures carry
 * their own PTAAssert checks; no expected result file is compared.
 */
public class ReflectionSoundnessTest {

    private static final String DIR = "reflsound";

    private static final String MEMBERS = "reflection-members:true";

    @Test
    void onlyTheArgumentCountRulesOutATarget() {
        Tests.testPTA(false, DIR, "TypeMatch");
    }

    @Test
    void getMethodFindsTheMethodsOfTheSuperinterfaces() {
        Tests.testPTA(false, DIR, "GetMethodIface");
    }

    @Test
    void memberArraysAndFieldLookupsReachTheMembers() {
        Tests.testPTA(false, DIR, "MemberArrays", MEMBERS);
    }

    @Test
    void withoutTheMembersOptionTheMembersAreNotModelled() {
        AssertionError error = assertThrows(AssertionError.class,
                () -> Tests.testPTA(false, DIR, "MemberArrays"));
        assertTrue(error.getMessage().contains("MaListed: void listed()"),
                error.getMessage());
    }

    @Test
    void reflectiveStaticUseInitializesTheClass() {
        Tests.testPTA(false, DIR, "ClassInit", MEMBERS);
    }
}
