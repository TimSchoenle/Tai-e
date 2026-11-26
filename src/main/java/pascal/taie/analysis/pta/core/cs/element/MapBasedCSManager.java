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

package pascal.taie.analysis.pta.core.cs.element;

import org.jspecify.annotations.Nullable;
import pascal.taie.World;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.Indexer;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Streams;
import pascal.taie.util.collection.TwoKeyMap;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * Manages data by maintaining the data and their context-sensitive
 * counterparts by maps.
 */
public class MapBasedCSManager implements CSManager {

    private final PointerManager ptrManager = new PointerManager();

    private final CSObjManager objManager = new CSObjManager();

    private final ContextElementMap<Invoke, CSCallSite> callSites = new ContextElementMap<>();

    private final TwoKeyMap<JMethod, Context, CSMethod> methods = Maps.newTwoKeyMap();

    @Override
    public CSVar getCSVar(Context context, Var var) {
        return ptrManager.getCSVar(context, var);
    }

    @Override
    public StaticField getStaticField(JField field) {
        return ptrManager.getStaticField(field);
    }

    /**
     * The base mapping of {@link #unifyInstanceFieldBases}, or {@code null}
     * when every object has its own instance fields.
     */
    private @Nullable UnaryOperator<CSObj> unifiedBase;

    @Override
    public InstanceField getInstanceField(CSObj base, JField field) {
        UnaryOperator<CSObj> unify = unifiedBase;
        return ptrManager.getInstanceField(unify == null ? base : unify.apply(base), field);
    }

    @Override
    public void unifyInstanceFieldBases(UnaryOperator<CSObj> unifiedBase) {
        if (this.unifiedBase != null) {
            throw new IllegalStateException("instance field bases already unified");
        }
        if (!ptrManager.getInstanceFields().isEmpty()) {
            throw new IllegalStateException("instance fields exist before the unification");
        }
        this.unifiedBase = unifiedBase;
    }

    @Override
    public ArrayIndex getArrayIndex(CSObj array) {
        return ptrManager.getArrayIndex(array);
    }

    @Override
    public MockPointer getMockPointer(PointerDescriptor descriptor,
                                      Object allocation, Type type) {
        return ptrManager.getMockPointer(descriptor, allocation, type);
    }

    @Override
    public Collection<Var> getVars() {
        return ptrManager.getVars();
    }

    @Override
    public Collection<CSVar> getCSVars() {
        return ptrManager.getCSVars();
    }

    @Override
    public Collection<CSVar> getCSVarsOf(Var var) {
        return ptrManager.getCSVarsOf(var);
    }

    @Override
    public Collection<StaticField> getStaticFields() {
        return ptrManager.getStaticFields();
    }

    @Override
    public Collection<InstanceField> getInstanceFields() {
        return ptrManager.getInstanceFields();
    }

    @Override
    public Collection<ArrayIndex> getArrayIndexes() {
        return ptrManager.getArrayIndexes();
    }

    @Override
    public Stream<Pointer> pointers() {
        return ptrManager.pointers();
    }

    @Override
    public Stream<MockPointer> mockPointers() {
        return ptrManager.mockPointers.values().stream();
    }

    @Override
    public CSObj getCSObj(Context heapContext, Obj obj) {
        return objManager.getCSObj(heapContext, obj);
    }

    @Override
    public Collection<CSObj> getObjects() {
        return objManager.getObjects();
    }

    @Override
    public Collection<CSObj> getCSObjsOf(Obj obj) {
        return objManager.getCSObjsOf(obj);
    }

    @Override
    public Indexer<CSObj> getObjectIndexer() {
        return objManager;
    }

    @Override
    public int getNumberOfPointers() {
        return ptrManager.counter;
    }

    /**
     * @return how many throwable {@link CSObj}s got an index so far, and
     * whether and when their reserved index range ran out.
     */
    public ThrowableCensus getThrowableCensus() {
        return objManager.getThrowableCensus();
    }

    /**
     * Census of the throwable {@link CSObj}s of this manager.
     *
     * @param throwableObjects          number of throwable {@link CSObj}s
     *                                  that got an index
     * @param budget                    number of indexes reserved for
     *                                  throwable objects
     * @param budgetExceededAfterMillis milliseconds from the creation of
     *                                  this manager until the first throwable
     *                                  object took an index outside the
     *                                  reserved range; -1 if none did
     */
    public record ThrowableCensus(int throwableObjects, int budget,
                                  long budgetExceededAfterMillis) {

        /**
         * @return whether a throwable object took an index outside the
         * reserved range.
         */
        public boolean budgetExceeded() {
            return budgetExceededAfterMillis >= 0;
        }
    }

    @Override
    public CSCallSite getCSCallSite(Context context, Invoke callSite) {
        CSCallSite csCallSite = callSites.get(callSite, context);
        if (csCallSite == null) {
            CSMethod container = getCSMethod(context, callSite.getContainer());
            csCallSite = new CSCallSite(callSite, context, container);
            callSites.add(callSite, csCallSite);
        }
        return csCallSite;
    }

    @Override
    public CSMethod getCSMethod(Context context, JMethod method) {
        return methods.computeIfAbsent(method, context, CSMethod::new);
    }

    private static class PointerManager {

        private final ContextElementMap<Var, CSVar> vars = new ContextElementMap<>();

        private final Map<JField, StaticField> staticFields = Maps.newMap();

        private final TwoKeyMap<CSObj, JField, InstanceField> instanceFields = Maps.newTwoKeyMap();

        private final Map<CSObj, ArrayIndex> arrayIndexes = Maps.newMap();

        private final Map<MockPointerKey, MockPointer> mockPointers = Maps.newMap();

        private record MockPointerKey(PointerDescriptor descriptor,
                                      Object allocation,
                                      Type type) {
        }

        /**
         * Counter for assigning unique indexes to Pointers.
         */
        private int counter = 0;

        private CSVar getCSVar(Context context, Var var) {
            CSVar csVar = vars.get(var, context);
            if (csVar == null) {
                csVar = new CSVar(var, context, counter++);
                vars.add(var, csVar);
            }
            return csVar;
        }

        private StaticField getStaticField(JField field) {
            return staticFields.computeIfAbsent(field,
                    f -> new StaticField(f, counter++));
        }

        private InstanceField getInstanceField(CSObj base, JField field) {
            return instanceFields.computeIfAbsent(base, field,
                    (b, f) -> new InstanceField(b, f, counter++));
        }

        private ArrayIndex getArrayIndex(CSObj array) {
            return arrayIndexes.computeIfAbsent(array,
                    a -> new ArrayIndex(a, counter++));
        }

        private MockPointer getMockPointer(PointerDescriptor descriptor,
                                           Object allocation, Type type) {
            MockPointerKey key = new MockPointerKey(descriptor, allocation, type);
            return mockPointers.computeIfAbsent(key,
                    k -> new MockPointer(descriptor, allocation, type, counter++));
        }

        private Collection<Var> getVars() {
            return vars.keySet();
        }

        private Collection<CSVar> getCSVars() {
            return vars.values();
        }

        private Collection<CSVar> getCSVarsOf(Var var) {
            return vars.valuesOf(var);
        }

        private Collection<StaticField> getStaticFields() {
            return Collections.unmodifiableCollection(staticFields.values());
        }

        private Collection<InstanceField> getInstanceFields() {
            return instanceFields.values();
        }

        private Collection<ArrayIndex> getArrayIndexes() {
            return Collections.unmodifiableCollection(arrayIndexes.values());
        }

        private Stream<Pointer> pointers() {
            return Streams.concat(
                    getCSVars().stream(),
                    getInstanceFields().stream(),
                    getArrayIndexes().stream(),
                    getStaticFields().stream());
        }
    }

    private static class CSObjManager implements Indexer<CSObj> {

        private final TwoKeyMap<Obj, Context, CSObj> objMap = Maps.newTwoKeyMap();

        private final TypeSystem typeSystem = World.get().getTypeSystem();

        private final Type throwable = typeSystem.throwableType();

        private final Type string = typeSystem.stringType();

        /**
         * Counter for assign unique indexes to throwable objects.
         */
        private int throwableCounter = 0;

        /**
         * Number of indexes reserved for throwable objects.
         */
        private static final int THROWABLE_BUDGET = 2048;

        /**
         * Counter for assign unique indexes to string objects.
         */
        private int stringCounter = THROWABLE_BUDGET;

        /**
         * Number of indexes reserved for string objects.
         */
        private static final int STRING_BUDGET = 4096;

        /**
         * Counter for assigning unique indexes to other CSObjs.
         */
        private int counter = THROWABLE_BUDGET + STRING_BUDGET;

        /**
         * Maps index to CSObj.
         * Since there are empty slots, using array (instead of List)
         * is more convenient.
         */
        private CSObj[] objs = new CSObj[65536];

        /**
         * Time of creation of this manager, for {@link #budgetExceededAfterMillis}.
         */
        private final long createdNanos = System.nanoTime();

        /**
         * Number of throwable objects that got an index, inside or outside
         * the reserved range.
         */
        private int throwableObjects = 0;

        /**
         * Milliseconds from {@link #createdNanos} until the first throwable
         * object took an index outside the reserved range; -1 if none did.
         */
        private long budgetExceededAfterMillis = -1;

        ThrowableCensus getThrowableCensus() {
            return new ThrowableCensus(throwableObjects, THROWABLE_BUDGET,
                    budgetExceededAfterMillis);
        }

        CSObj getCSObj(Context heapContext, Obj obj) {
            return objMap.computeIfAbsent(obj, heapContext, (o, c) -> {
                int index = getCSObjIndex(o);
                CSObj csObj = new CSObj(o, c, index);
                storeCSObj(csObj, index);
                return csObj;
            });
        }

        private int getCSObjIndex(Obj obj) {
            if (typeSystem.isSubtype(throwable, obj.getType())) {
                ++throwableObjects;
                if (throwableCounter < THROWABLE_BUDGET) {
                    return throwableCounter++;
                }
                if (budgetExceededAfterMillis < 0) {
                    budgetExceededAfterMillis = TimeUnit.NANOSECONDS.toMillis(
                            System.nanoTime() - createdNanos);
                }
                return counter++;
            } else if (obj.getType().equals(string) &&
                    stringCounter < THROWABLE_BUDGET + STRING_BUDGET) {
                return stringCounter++;
            } else {
                return counter++;
            }
        }

        /**
         * Stores {@code csObj} to the {@code objs} array with the position
         * specified by {@code index}.
         */
        private void storeCSObj(CSObj csObj, int index) {
            if (index >= objs.length) {
                int newLength = Math.max(index + 1, (int) (objs.length * 1.5));
                objs = Arrays.copyOf(objs, newLength);
            }
            objs[index] = csObj;
        }

        Collection<CSObj> getObjects() {
            return objMap.values();
        }

        Collection<CSObj> getCSObjsOf(Obj obj) {
            var csObjs = objMap.get(obj);
            return csObjs != null ? csObjs.values() : Set.of();
        }

        @Override
        public int getIndex(CSObj o) {
            return o.getIndex();
        }

        @Override
        public CSObj getObject(int index) {
            return objs[index];
        }
    }
}
