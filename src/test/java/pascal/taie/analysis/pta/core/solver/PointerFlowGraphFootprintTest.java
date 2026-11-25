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

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import pascal.taie.Main;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.plugin.Plugin;

import java.lang.reflect.Field;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Layout of the pointer flow graph's out-edge store after an analysis of
 * the whole JDK (context-insensitive) and of the application only
 * (1-object): every used entry of every out-edge array is two slots, an
 * edge object and null, or a target and a tag (a {@link FlowKind} or a
 * {@link TypeFilter.EdgeTag}). Prints the bytes per edge of the edge
 * arrays, of the dedup sets and of the type filters' tags (array header
 * 16 bytes, object header 12 bytes, 4-byte references, 8-byte alignment)
 * for the comparison of layouts.
 */
public class PointerFlowGraphFootprintTest {

    @ParameterizedTest
    @CsvSource(delimiter = '|', value = {
            "src/test/resources/pta/lambda|ImpreciseLambdas|implicit-entries:true;"
                    + "only-app:false;handle-invokedynamic:true;",
            "src/test/resources/pta/lambda|LambdaContexts|cs:1-obj;implicit-entries:false;"
                    + "handle-invokedynamic:true;",
    })
    void everyOutEdgeTakesTwoSlots(String classPath, String main, String options) {
        FootprintProbe.edges = -1;
        FootprintProbe.malformed = -1;
        Main.main("-java", "8", "-cp", classPath, "-m", main, "-a",
                "pta=" + options + "plugins:[" + FootprintProbe.class.getName() + "];");
        assertTrue(FootprintProbe.edges > 0, "no out edge measured");
        assertEquals(0, FootprintProbe.malformed,
                "edge arrays not made of (edge, null) and (target, tag) pairs");
    }

    private static long align(long bytes) {
        return (bytes + 7) & ~7L;
    }

    private static long arrayBytes(int length) {
        return align(16L + 4L * length);
    }

    /**
     * @return whether the array is a sequence of two-slot entries: an edge
     * object and null, a target and a tag, or two nulls (unused, at the end
     * only).
     */
    private static boolean wellFormed(Object[] slots, Set<TypeFilter.EdgeTag> tags) {
        if (slots.length % 2 != 0) {
            return false;
        }
        boolean unused = false;
        for (int i = 0; i < slots.length; i += 2) {
            Object first = slots[i];
            Object tag = slots[i + 1];
            if (first == null) {
                unused = true;
                if (tag != null) {
                    return false;
                }
            } else if (unused) {
                return false;
            } else if (first instanceof PointerFlowEdge) {
                if (tag != null) {
                    return false;
                }
            } else if (first instanceof Pointer) {
                if (tag instanceof TypeFilter.EdgeTag edgeTag) {
                    tags.add(edgeTag);
                } else if (!(tag instanceof FlowKind)) {
                    return false;
                }
            } else {
                return false;
            }
        }
        return true;
    }

    /**
     * Sums, at onFinish, the out degrees and the bytes of the out-edge
     * arrays and dedup sets of all pointers, mock pointers included, and
     * of the tags the type filters hold for them.
     */
    public static class FootprintProbe implements Plugin {

        static long edges;

        static long malformed;

        private Solver solver;

        @Override
        public void setSolver(Solver solver) {
            this.solver = solver;
        }

        @Override
        public void onFinish() {
            try {
                measure();
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }

        private void measure() throws ReflectiveOperationException {
            CSManager csManager = solver.getCSManager();
            Class<?> type = Class.forName(
                    "pascal.taie.analysis.pta.core.cs.element.AbstractPointer");
            Field edgesField = type.getDeclaredField("edges");
            Field dedupField = type.getDeclaredField("dedup");
            edgesField.setAccessible(true);
            dedupField.setAccessible(true);
            Set<TypeFilter.EdgeTag> tags = Collections.newSetFromMap(new IdentityHashMap<>());
            long count = 0;
            long bad = 0;
            long slots = 0;
            long edgeBytes = 0;
            long dedupBytes = 0;
            for (Pointer p : Stream.concat(csManager.pointers(), csManager.mockPointers()).toList()) {
                count += p.getOutDegree();
                Object[] array = (Object[]) edgesField.get(p);
                if (array != null) {
                    slots += array.length;
                    edgeBytes += arrayBytes(array.length);
                    if (!wellFormed(array, tags)) {
                        ++bad;
                    }
                }
                Object set = dedupField.get(p);
                if (set instanceof byte[] bytes) {
                    dedupBytes += align(16L + bytes.length);
                } else if (set instanceof char[] chars) {
                    dedupBytes += align(16L + 2L * chars.length);
                } else if (set instanceof int[] ints) {
                    dedupBytes += arrayBytes(ints.length);
                } else if (set != null) {
                    // the dedup state after a removal: this analysis removes no edge
                    ++bad;
                }
            }
            Field filtersField = DefaultSolver.class.getDeclaredField("typeFilters");
            filtersField.setAccessible(true);
            int filters = ((Map<?, ?>) filtersField.get(solver)).size();
            Map<TypeFilter, Integer> tagsPerFilter = new IdentityHashMap<>();
            tags.forEach(t -> tagsPerFilter.merge(t.filter(), 1, Integer::sum));
            long multiKind = tagsPerFilter.values().stream().filter(n -> n > 1).count();
            // two reference fields per filter (upper bound: they may fit
            // into padding), one tag object each, one array per filter
            // with tags of more than one kind
            long tagBytes = 8L * filters + align(12 + 8) * tags.size()
                    + arrayBytes(FlowKind.values().length) * multiKind;
            edges = count;
            malformed = bad;
            System.out.printf("PFG footprint: edges=%d slots=%d edge_array_bytes=%d"
                            + " dedup_bytes=%d type_filters=%d tags=%d multi_kind_filters=%d"
                            + " tag_bytes=%d edge_bytes_per_edge=%.2f dedup_bytes_per_edge=%.2f"
                            + " tag_bytes_per_edge=%.2f%n",
                    count, slots, edgeBytes, dedupBytes, filters, tags.size(), multiKind,
                    tagBytes, (double) edgeBytes / count, (double) dedupBytes / count,
                    (double) tagBytes / count);
        }
    }
}
