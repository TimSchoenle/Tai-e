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

package pascal.taie.analysis.pta.plugin.invokedynamic;

import org.junit.jupiter.api.Test;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.TestCallSites;
import pascal.taie.ir.exp.InvokeDynamic;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The open-addressing chain tables of {@link LambdaAnalysis} against the
 * maps they replace: the sequence of interned sources (by identity) and of
 * call decisions must equal that of a {@code HashMap} keyed by
 * (base, arguments) and a {@code HashSet} of (call site, source) records.
 */
class ChainTablesTest {

    private static final int CONTEXTS = 25;

    private static final int INDYS = 20;

    /** The variables the argument lists draw from. */
    private static final int ARG_VARS = 3;

    private static final int MAX_ARGS = 2;

    private static final int STEPS = 20_000;

    /** A context compared by value, so equal contexts need not be the same. */
    private record ValueContext(int id) implements Context {
        @Override
        public int getLength() {
            return 1;
        }

        @Override
        public Object getElementAt(int i) {
            return id;
        }
    }

    private record ReferenceKey(LambdaSource base, List<CSVar> args) {
    }

    private record ReferenceCall(CSCallSite site, LambdaSource source) {
    }

    @Test
    void internsAndDecidesLikeTheReferenceMaps() {
        Random random = new Random(116);
        List<InvokeDynamic> indys = new ArrayList<>();
        for (int i = 0; i < INDYS; ++i) {
            indys.add(new InvokeDynamic(null, null, "m" + i, null, List.of(), List.of()));
        }
        List<CSCallSite> sites = new ArrayList<>();
        for (int i = 0; i < 30; ++i) {
            sites.add(TestCallSites.detached(new ValueContext(i)));
        }
        List<CSVar> vars = new ArrayList<>();
        for (int i = 0; i < ARG_VARS; ++i) {
            vars.add(TestCallSites.detachedVar(new ValueContext(i), i));
        }
        ChainedSources table = new ChainedSources();
        ChainedCalls calls = new ChainedCalls();
        Map<ReferenceKey, LambdaSource> reference = new HashMap<>();
        Set<ReferenceCall> referenceCalls = new HashSet<>();
        // reference source -> interned source: the identity sequences must match
        Map<LambdaSource, LambdaSource> pairing = new IdentityHashMap<>();
        for (int step = 0; step < STEPS; ++step) {
            InvokeDynamic indy = indys.get(random.nextInt(indys.size()));
            int contextId = random.nextInt(CONTEXTS);
            // a new, equal context each time: interning must compare values
            Context context = new ValueContext(contextId);
            // a fresh scratch list each time, equal to earlier ones but not
            // the same: interning must compare values and keep its own copy
            List<CSVar> args = new ArrayList<>();
            int argCount = random.nextInt(MAX_ARGS + 1);
            for (int a = 0; a < argCount; ++a) {
                args.add(vars.get(random.nextInt(vars.size())));
            }
            List<CSVar> argsCopy = List.copyOf(args);
            LambdaSource base = new LambdaSource(indy, context);
            LambdaSource expected = reference.computeIfAbsent(new ReferenceKey(base, argsCopy),
                    k -> new LambdaSource(indy, base.getContext(), argsCopy));
            LambdaSource found = table.find(indy, context, args);
            LambdaSource interned = table.intern(indy, context, args);
            if (found != null) {
                assertSame(found, interned, "find agrees with intern");
            }
            args.clear();
            assertEquals(argsCopy, interned.getSamArgs(), "own copy of the arguments");
            LambdaSource paired = pairing.computeIfAbsent(expected, e -> interned);
            assertSame(paired, interned, "identity sequence at step " + step);
            assertEquals(expected, interned, "value at step " + step);
            CSCallSite site = sites.get(random.nextInt(sites.size()));
            ReferenceCall call = new ReferenceCall(site, expected);
            assertEquals(referenceCalls.contains(call), calls.contains(site, interned),
                    "contains before add at step " + step);
            boolean expectedAdd = referenceCalls.add(call);
            assertEquals(expectedAdd, calls.add(site, interned),
                    "call decision at step " + step);
            assertTrue(calls.contains(site, interned), "contains after add");
        }
        assertEquals(reference.size(), table.size(), "interned sources");
        assertEquals(referenceCalls.size(), calls.size(), "calls");
        assertTrue(reference.size() < STEPS * 3 / 4, "sources repeat: " + reference.size());
        Set<LambdaSource> identities = Collections.newSetFromMap(new IdentityHashMap<>());
        for (ReferenceKey key : reference.keySet()) {
            LambdaSource s = table.find(key.base().getIndy(),
                    new ValueContext(((ValueContext) key.base().getContext()).id()),
                    new ArrayList<>(key.args()));
            assertNotNull(s, "find of " + key);
            identities.add(s);
        }
        assertEquals(reference.size(), identities.size(), "one object per source value");
        table.clear();
        calls.clear();
        assertNull(table.find(indys.get(0), new ValueContext(0), List.of()));
        assertEquals(0, calls.size());
    }
}
