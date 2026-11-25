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

import org.jspecify.annotations.Nullable;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MockPointer;
import pascal.taie.analysis.pta.core.cs.element.RelayDescriptor;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.util.AnalysisModelPlugin;
import pascal.taie.analysis.pta.plugin.util.CSObjs;
import pascal.taie.analysis.pta.plugin.util.InvokeHandler;
import pascal.taie.analysis.pta.plugin.util.InvokeUtils;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.NewArray;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.New;
import pascal.taie.language.classes.ClassNames;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.ReferenceType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.VoidType;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;

import static pascal.taie.analysis.graph.flowgraph.FlowKind.INSTANCE_STORE;
import static pascal.taie.analysis.graph.flowgraph.FlowKind.PARAMETER_PASSING;
import static pascal.taie.analysis.graph.flowgraph.FlowKind.RETURN;
import static pascal.taie.analysis.graph.flowgraph.FlowKind.STATIC_STORE;
import static pascal.taie.analysis.pta.plugin.util.InvokeUtils.BASE;

/**
 * Models reflective-action methods, currently supports
 * <ul>
 *     <li>Class.newInstance()
 *     <li>Constructor.newInstance(Object[])
 *     <li>Method.invoke(Object,Object[])
 *     <li>Field.get(Object)
 *     <li>Field.set(Object,Object)
 *     <li>Array.newInstance(Class,int)
 *     <li>Array.newInstance(Class,int[])
 * </ul>
 * TODO: check accessibility
 */
public class ReflectiveActionModel extends AnalysisModelPlugin {

    /**
     * Descriptor for objects created by reflective newInstance() calls.
     */
    private static final Descriptor REF_OBJ_DESC = () -> "ReflectiveObj";

    private final Subsignature initNoArg;

    private final MetaObjHelper helper;

    private final TypeMatcher typeMatcher;

    /**
     * Descriptor of the relay pointers of reflective argument passing.
     */
    private static final RelayDescriptor ARGS_RELAY_DESC = () -> "ReflectiveArgsRelay";

    /**
     * Associates argument variable (Object[]) to its relay pointer, which
     * receives the elements of every array the variable points to and
     * passes them to the parameters of every reflective callee of the
     * calls that use the variable. One relay per (context, variable)
     * replaces one edge per (array, callee parameter) pair: the
     * parameters receive the same union of elements under the same type
     * filter.
     */
    private final Map<CSVar, MockPointer> argsRelays = Maps.newMap();

    /**
     * Checks the relays against the edges they replace; present only when
     * {@code -Dpx.reflargs.verify=true}.
     */
    private final @Nullable ReflectiveArgsVerifier verifier;

    /**
     * Set of invocations that are annotated by the reflection log.
     */
    private final Set<Invoke> invokesWithLog;

    /**
     * Records all reflective targets resolved by reflection analysis.
     */
    private final MultiMap<Invoke, Object> allTargets = Maps.newMultiMap();

    private final SupertypeClosure supertypes;

    /**
     * The state of each {@code Method.invoke} call site in each context.
     */
    private final Map<CSCallSite, InstanceSite<JMethod>> invokeSites = Maps.newMap();

    /**
     * The state of each {@code Field.get} and {@code Field.set} call site in
     * each context.
     */
    private final Map<CSCallSite, InstanceSite<JField>> fieldSites = Maps.newMap();

    ReflectiveActionModel(Solver solver, MetaObjHelper helper,
                          TypeMatcher typeMatcher, Set<Invoke> invokesWithLog) {
        super(solver);
        supertypes = new SupertypeClosure(hierarchy);
        initNoArg = Subsignature.getNoArgInit();
        this.helper = helper;
        this.typeMatcher = typeMatcher;
        this.invokesWithLog = invokesWithLog;
        this.verifier = ReflectiveArgsVerifier.isEnabled()
                ? new ReflectiveArgsVerifier(solver, argsRelays)
                : null;
    }

    @InvokeHandler(signature = "<java.lang.Class: java.lang.Object newInstance()>", argIndexes = {BASE})
    public void classNewInstance(Context context, Invoke invoke, PointsToSet classes) {
        classes.forEach(obj -> {
            if (isInvalidTarget(invoke, obj)) {
                return;
            }
            JClass clazz = CSObjs.toClass(obj);
            if (clazz != null) {
                JMethod init = clazz.getDeclaredMethod(initNoArg);
                if (init != null && !typeMatcher.isUnmatched(invoke, init)) {
                    ClassType type = clazz.getType();
                    CSObj csNewObj = newReflectiveObj(context, invoke, type);
                    addReflectiveCallEdge(context, invoke, csNewObj, init, null);
                }
            }
        });
    }

    @InvokeHandler(signature = "<java.lang.reflect.Constructor: java.lang.Object newInstance(java.lang.Object[])>", argIndexes = {BASE})
    public void constructorNewInstance(Context context, Invoke invoke, PointsToSet constructors) {
        constructors.forEach(obj -> {
            if (isInvalidTarget(invoke, obj)) {
                return;
            }
            JMethod constructor = CSObjs.toConstructor(obj);
            if (constructor != null && !typeMatcher.isUnmatched(invoke, constructor)) {
                ClassType type = constructor.getDeclaringClass().getType();
                CSObj csNewObj = newReflectiveObj(context, invoke, type);
                addReflectiveCallEdge(context, invoke, csNewObj,
                        constructor, invoke.getInvokeExp().getArg(0));
            }
        });
    }

    private CSObj newReflectiveObj(Context context, Invoke invoke, ReferenceType type) {
        Obj newObj = heapModel.getMockObj(REF_OBJ_DESC,
                invoke, type, invoke.getContainer());
        // TODO: double-check if the heap context is proper
        CSObj csNewObj = csManager.getCSObj(context, newObj);
        Var result = invoke.getResult();
        if (result != null) {
            solver.addVarPointsTo(context, result, csNewObj);
        }
        return csNewObj;
    }

    /**
     * {@code Method.invoke} pairs every Method object with every receiver,
     * and is called again whenever either set grows. Each instance target
     * meets each receiver of a subtype of its declaring class once, when
     * the later of the two arrives (see {@link MemberReceiverIndex}); a
     * receiver of another type makes the JVM throw, and
     * {@code ClassHierarchy.dispatch} answers {@code null} for it.
     */
    @InvokeHandler(signature = "<java.lang.reflect.Method: java.lang.Object invoke(java.lang.Object,java.lang.Object[])>", argIndexes = {BASE, 0})
    public void methodInvoke(Context context, Invoke invoke,
                             PointsToSet mtdObjs, PointsToSet recvObjs) {
        Var argsVar = invoke.getInvokeExp().getArg(1);
        InstanceSite<JMethod> site = site(invokeSites, context, invoke, JMethod::getDeclaringClass);
        MemberReceiverIndex.PairAction<JMethod, CSObj> call = (target, type, receivers) ->
                addDispatchedCallEdges(context, invoke, target, type, receivers, argsVar);
        site.index().addReceivers(
                site.receivers().unseen(recvObjs, argPointsTo(context, invoke, 0)), call);
        for (CSObj mtdObj : site.members().unseen(mtdObjs, argPointsTo(context, invoke, BASE))) {
            if (isInvalidTarget(invoke, mtdObj)) {
                continue;
            }
            JMethod target = CSObjs.toMethod(mtdObj);
            if (target != null && !typeMatcher.isUnmatched(invoke, target)) {
                if (target.isStatic()) {
                    addReflectiveCallEdge(context, invoke, null, target, argsVar);
                } else {
                    site.index().addMember(target, call);
                }
            }
        }
    }

    /**
     * {@code Field.get}: pairs fields and base objects like
     * {@link #methodInvoke}.
     */
    @InvokeHandler(signature = "<java.lang.reflect.Field: java.lang.Object get(java.lang.Object)>", argIndexes = {BASE, 0})
    public void fieldGet(Context context, Invoke invoke,
                         PointsToSet fldObjs, PointsToSet baseObjs) {
        Var result = invoke.getResult();
        if (result == null) {
            return;
        }
        CSVar to = csManager.getCSVar(context, result);
        accessFields(context, invoke, fldObjs, baseObjs,
                field -> {
                    StaticField sField = csManager.getStaticField(field);
                    solver.addPFGEdge(sField, to, FlowKind.STATIC_LOAD);
                },
                (field, type, bases) -> {
                    for (CSObj baseObj : bases) {
                        InstanceField ifield = csManager.getInstanceField(baseObj, field);
                        solver.addPFGEdge(ifield, to, FlowKind.INSTANCE_LOAD);
                        allTargets.put(invoke, field); // record target
                    }
                });
    }

    /**
     * {@code Field.set}: pairs fields and base objects like
     * {@link #methodInvoke}.
     */
    @InvokeHandler(signature = "<java.lang.reflect.Field: void set(java.lang.Object,java.lang.Object)>", argIndexes = {BASE, 0})
    public void fieldSet(Context context, Invoke invoke,
                         PointsToSet fldObjs, PointsToSet baseObjs) {
        CSVar from = csManager.getCSVar(context, invoke.getInvokeExp().getArg(1));
        accessFields(context, invoke, fldObjs, baseObjs,
                field -> {
                    StaticField sfield = csManager.getStaticField(field);
                    solver.addPFGEdge(new PointerFlowEdge(
                            STATIC_STORE, from, sfield),
                            sfield.getType());
                },
                (field, type, bases) -> {
                    for (CSObj baseObj : bases) {
                        InstanceField ifield = csManager.getInstanceField(baseObj, field);
                        solver.addPFGEdge(new PointerFlowEdge(
                                INSTANCE_STORE, from, ifield),
                                ifield.getType());
                        allTargets.put(invoke, field); // record target
                    }
                });
    }

    /**
     * Applies {@code staticAccess} to each new static field (after
     * initializing its class) and {@code instanceAccess} to each new pair of
     * an instance field and a base object of a subtype of its declaring
     * class.
     */
    private void accessFields(Context context, Invoke invoke,
                              PointsToSet fldObjs, PointsToSet baseObjs,
                              Consumer<JField> staticAccess,
                              MemberReceiverIndex.PairAction<JField, CSObj> instanceAccess) {
        InstanceSite<JField> site = site(fieldSites, context, invoke, JField::getDeclaringClass);
        site.index().addReceivers(
                site.receivers().unseen(baseObjs, argPointsTo(context, invoke, 0)), instanceAccess);
        for (CSObj fldObj : site.members().unseen(fldObjs, argPointsTo(context, invoke, BASE))) {
            if (isInvalidTarget(invoke, fldObj)) {
                continue;
            }
            JField field = CSObjs.toField(fldObj);
            if (field != null) {
                if (field.isStatic()) {
                    initializeDeclaringClass(field);
                    staticAccess.accept(field);
                } else {
                    site.index().addMember(field, instanceAccess);
                }
            }
        }
    }

    /**
     * The state of one {@code Method.invoke}, {@code Field.get} or
     * {@code Field.set} call site in one context: the member objects and
     * receiver objects taken so far, and the instance members paired with
     * the receivers.
     */
    private record InstanceSite<M>(SeenObjs members, SeenObjs receivers,
                                   MemberReceiverIndex<M, CSObj> index) {
    }

    private <M> InstanceSite<M> site(Map<CSCallSite, InstanceSite<M>> sites,
                                     Context context, Invoke invoke,
                                     Function<? super M, JClass> declaringClassOf) {
        CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
        InstanceSite<M> site = sites.get(csCallSite);
        if (site == null) {
            site = new InstanceSite<>(
                    new SeenObjs(solver.makePointsToSet()),
                    new SeenObjs(solver.makePointsToSet()),
                    new MemberReceiverIndex<>(supertypes, declaringClassOf,
                            recvObj -> recvObj.getObject().getType()));
            sites.put(csCallSite, site);
        }
        return site;
    }

    private PointsToSet argPointsTo(Context context, Invoke invoke, int index) {
        return SeenObjs.livePointsTo(solver, context, invoke, index);
    }

    @InvokeHandler(signature = {
            "<java.lang.reflect.Array: java.lang.Object newInstance(java.lang.Class,int)>",
            "<java.lang.reflect.Array: java.lang.Object newInstance(java.lang.Class,int[])>"
    }, argIndexes = {0, 1})
    public void arrayNewInstance(Context context, Invoke invoke, PointsToSet pts, PointsToSet arrayObjs) {
        Var result = invoke.getResult();
        if (result == null) {
            return;
        }
        pts.forEach(obj -> {
            if (isInvalidTarget(invoke, obj)) {
                return;
            }
            Type baseType = CSObjs.toType(obj);
            if (baseType != null && !(baseType instanceof VoidType)) {
                resolveArrayRanks(invoke, arrayObjs).forEach(rank ->
                        createReflectiveArray(context, invoke, baseType, rank));
            }
        });
    }

    private List<Integer> resolveArrayRanks(Invoke invoke, PointsToSet dimensionArrays) {
        List<Integer> ranks = new ArrayList<>();
        if (InvokeUtils.getVar(invoke, 1).getType() instanceof ArrayType) {
            dimensionArrays.forEach(arrayObj -> {
                Integer rank = getArrayRank(arrayObj);
                if (rank != null) {
                    ranks.add(rank);
                }
            });
        } else {
            ranks.add(1);
        }
        return ranks;
    }

    private static @Nullable Integer getArrayRank(CSObj arrayObj) {
        if (arrayObj.getObject().getAllocation() instanceof New stmt
                && stmt.getRValue() instanceof NewArray newArray
                && newArray.getLength().isConst()
                && newArray.getLength().getConstValue() instanceof IntLiteral intLiteral) {
            return intLiteral.getValue();
        }
        return null;
    }

    private void createReflectiveArray(
            Context context, Invoke invoke, Type baseType, int rank) {
        if (ReflectionAnalysis.ignoreImpreciseTarget(
                allTargets.get(invoke).size())) {
            return;
        }
        ArrayType arrayType = typeSystem.getArrayType(baseType, rank);
        CSObj csNewArray = newReflectiveObj(context, invoke, arrayType);
        allTargets.put(invoke, arrayType);
        if (rank > 1) {
            connectNestedArrays(context, invoke, csNewArray, arrayType, rank);
        }
    }

    private void connectNestedArrays(
            Context parentContext, Invoke invoke, CSObj parentArray,
            ArrayType parentType, int rank) {
        ArrayIndex parentIndex = csManager.getArrayIndex(parentArray);
        Type nestedType = parentType.elementType();
        for (int i = 1; i < rank; ++i) {
            Obj nestedArray = heapModel.getMockObj(
                    REF_OBJ_DESC, invoke + "[" + (i - 1) + "]",
                    nestedType, invoke.getContainer());
            Context nestedContext = selector.selectHeapContext(
                    csManager.getCSMethod(parentContext, invoke.getContainer()),
                    nestedArray);
            solver.addPointsTo(parentIndex, nestedContext, nestedArray);

            if (nestedType instanceof ArrayType arrayType) {
                CSObj nestedCSObj = csManager.getCSObj(parentContext, nestedArray);
                parentIndex = csManager.getArrayIndex(nestedCSObj);
                parentContext = nestedContext;
                nestedType = arrayType.elementType();
            }
        }
    }

    /**
     * Initializes the class that declares static field {@code field}, as
     * {@code Field.get} and {@code Field.set} of a static field do before
     * the access, like a direct static field access
     * ({@link pascal.taie.analysis.pta.plugin.ClassInitializer}). Without
     * it, a value only the static initializer stores never reaches the
     * reader (px/s115). A reflective static method or constructor target
     * needs no call here: {@code ClassInitializer.onNewMethod} initializes
     * its class when the target becomes reachable.
     */
    private void initializeDeclaringClass(JField field) {
        solver.initializeClass(field.getDeclaringClass());
    }

    /**
     * If a reflective invocation {@code invoke} is annotated by the log,
     * and the given {@code metaObj} is not generated by the log, then we treat
     * {@code metaObj} as an invalid target for {@code invoke}.
     */
    private boolean isInvalidTarget(Invoke invoke, CSObj metaObj) {
        return invokesWithLog.contains(invoke) && !helper.isLogMetaObj(metaObj);
    }

    /**
     * Whether a new target of {@code callSite} is ignored: the call site has
     * too many targets to be precise, or Android mode skips the non-application
     * {@code callee}. The target count is read only when imprecise targets are
     * ignored at all, and then again for every new target, as each recorded
     * target raises it.
     */
    private boolean isSkippedTarget(Invoke callSite, JMethod callee) {
        if (ReflectionAnalysis.ignoresImpreciseTargets()
                && ReflectionAnalysis.ignoreImpreciseTarget(allTargets.get(callSite).size())) {
            return true;
        }
        return ReflectionAnalysis.isAndroidMode() && !callee.isApplication();
    }

    /**
     * Adds the call edge of a constructor or a static method, which needs
     * no dispatch.
     */
    private void addReflectiveCallEdge(
            Context callerCtx, Invoke callSite,
            @Nullable CSObj recvObj, JMethod callee, Var args) {
        if (isSkippedTarget(callSite, callee)) {
            return;
        }
        addResolvedCallEdge(callerCtx, callSite, recvObj, callee, args);
    }

    /**
     * Adds the call edges of instance method {@code target} on
     * {@code receivers}, all of type {@code type}, dispatched once on that
     * type. The skip check stays per receiver: each edge added raises the
     * call site's target count that it reads.
     */
    private void addDispatchedCallEdges(
            Context callerCtx, Invoke callSite, JMethod target,
            Type type, Collection<CSObj> receivers, Var args) {
        JMethod callee = hierarchy.dispatch(type, target.getRef());
        if (callee == null) {
            return;
        }
        for (CSObj recvObj : receivers) {
            if (!isSkippedTarget(callSite, target)) {
                addResolvedCallEdge(callerCtx, callSite, recvObj, callee, args);
            }
        }
    }

    private void addResolvedCallEdge(
            Context callerCtx, Invoke callSite,
            @Nullable CSObj recvObj, JMethod callee, Var args) {
        CSCallSite csCallSite = csManager.getCSCallSite(callerCtx, callSite);
        Context calleeCtx;
        if (callee.isStatic()) {
            calleeCtx = selector.selectContext(csCallSite, callee);
        } else {
            calleeCtx = selector.selectContext(csCallSite, recvObj, callee);
            // pass receiver object to 'this' variable of callee
            solver.addVarPointsTo(calleeCtx, callee.getIR().getThis(), recvObj);
        }
        ReflectiveCallEdge callEdge = new ReflectiveCallEdge(csCallSite,
                csManager.getCSMethod(calleeCtx, callee), args);
        solver.addCallEdge(callEdge);
        allTargets.put(callSite, callee); // record target
    }

    @Override
    public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (edge instanceof ReflectiveCallEdge refEdge) {
            Context callerCtx = refEdge.getCallSite().getContext();
            // pass argument
            Var args = refEdge.getArgs();
            if (args != null) {
                CSVar csArgs = csManager.getCSVar(callerCtx, args);
                passReflectiveArgs(refEdge, getArgsRelay(csArgs));
                if (verifier != null) {
                    verifier.addEdge(csArgs, refEdge);
                }
            }
            // pass return value
            Invoke invoke = refEdge.getCallSite().getCallSite();
            Context calleeCtx = refEdge.getCallee().getContext();
            JMethod callee = refEdge.getCallee().getMethod();
            Var result = invoke.getResult();
            if (result != null && isConcerned(callee.getReturnType())) {
                CSVar csResult = csManager.getCSVar(callerCtx, result);
                callee.getIR().getReturnVars().forEach(ret -> {
                    CSVar csRet = csManager.getCSVar(calleeCtx, ret);
                    solver.addPFGEdge(csRet, csResult, RETURN);
                });
            }
        }
    }

    /**
     * Returns the relay pointer of the given argument variable. A new relay
     * receives the elements of the arrays the variable points to now;
     * {@link #onNewPointsToSet} connects the arrays that arrive later.
     */
    private MockPointer getArgsRelay(CSVar csArgs) {
        MockPointer relay = argsRelays.get(csArgs);
        if (relay == null) {
            relay = csManager.getMockPointer(ARGS_RELAY_DESC, csArgs,
                    typeSystem.getClassType(ClassNames.OBJECT));
            argsRelays.put(csArgs, relay);
            connectArrays(relay, solver.getPointsToSetOf(csArgs));
        }
        return relay;
    }

    private void connectArrays(MockPointer relay, PointsToSet arrays) {
        arrays.forEach(array -> solver.addPFGEdge(
                csManager.getArrayIndex(array), relay, PARAMETER_PASSING));
    }

    private void passReflectiveArgs(ReflectiveCallEdge edge, MockPointer relay) {
        Context calleeCtx = edge.getCallee().getContext();
        JMethod callee = edge.getCallee().getMethod();
        callee.getIR().getParams().forEach(param -> {
            Type paramType = param.getType();
            if (isConcerned(paramType)) {
                CSVar csParam = csManager.getCSVar(calleeCtx, param);
                solver.addPFGEdge(new PointerFlowEdge(
                                PARAMETER_PASSING, relay, csParam),
                        paramType);
            }
        });
    }

    static boolean isConcerned(Type type) {
        return type instanceof ClassType || type instanceof ArrayType;
    }

    @Override
    public void onNewPointsToSet(CSVar csVar, PointsToSet pts) {
        super.onNewPointsToSet(csVar, pts);
        MockPointer relay = argsRelays.get(csVar);
        if (relay != null) {
            connectArrays(relay, pts);
        }
        if (verifier != null) {
            verifier.onProgress();
        }
    }

    @Override
    public void onPhaseFinish() {
        if (verifier != null) {
            // another plugin may still add work in its own onPhaseFinish
            verifier.verify(false);
        }
    }

    @Override
    public void onFinish() {
        if (verifier != null) {
            if (solver.isStoppedByTimeLimit()) {
                // work is left on the work list: only the running check applies
                verifier.verify(false);
            } else {
                verifier.verify(true);
            }
        }
    }

    MultiMap<Invoke, Object> getAllTargets() {
        return allTargets;
    }
}
