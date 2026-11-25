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

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.DefaultSolver;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.plugin.util.CSObjs;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.InvokeDynamic;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.MethodHandle;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.ClassNames;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Signatures;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

public class LambdaAnalysis implements Plugin {

    /**
     * Descriptor for lambda functional objects.
     */
    private static final Descriptor LAMBDA_DESC = () -> "LambdaObj";

    /**
     * Descriptor for objects created by lambda constructor.
     */
    private static final Descriptor LAMBDA_NEW_DESC = () -> "LambdaConstructedObj";

    private Solver solver;

    private HeapModel heapModel;

    private ContextSelector selector;

    private ClassHierarchy hierarchy;

    private CSManager csManager;

    /**
     * Whether the selector selects the context of an instance call without
     * its call site ({@link ContextSelector#isInstanceContextCallSiteFree}),
     * so that the invocations of one target method reference on a receiver
     * variable share one grouping ({@link #addSharedLambdaCallEdges}).
     */
    private boolean callSiteFreeContexts;

    /**
     * Option that selects the heap context of lambda functional objects:
     * {@code method} (the context of the method that created the object) or
     * {@code captured} ({@link #capturedArgsContext}: the empty context when
     * the lambda captures no variable). Under context selectors of limit 1
     * {@code captured} keeps the call graph and the points-to sets projected
     * to objects, unless a lambda object is the base of a field or array
     * access; a selector of limit 2 puts the receiver's heap context into
     * the callee context, so calls on capture-free lambda objects (default
     * methods, lambda self receivers) then have fewer callee contexts.
     */
    private static final String HEAP_CONTEXT_OPTION = "lambda-heap-context";

    /**
     * Whether the option {@link #HEAP_CONTEXT_OPTION} is {@code captured}.
     */
    private boolean capturedHeapContext;

    /**
     * Map from method to the lambda functional objects created in the method.
     */
    private final MultiMap<JMethod, Obj> lambdaObjs = Maps.newMultiMap();

    /**
     * Map from receiver variable to the information about the related
     * instance invocation sites. When new objects reach the receiver variable,
     * this information will be used to build lambda call edges.
     */
    private final MultiMap<CSVar, InstanceInvoInfo> invoInfos = Maps.newMultiMap();

    /**
     * Map from each receiver variable of {@link #invoInfos} to its points-to
     * set grouped by object type, so that a lambda object reaching another
     * invocation site on that variable does not regroup the whole set.
     * Created from the variable's points-to set at its first lambda
     * invocation and extended by every new points-to set of the variable
     * ({@link #onNewPointsToSet}). The solver changes a variable's points-to
     * set only when it propagates a work-list entry, and notifies
     * {@link #onNewPointsToSet} of the difference before it takes the next
     * entry; in between it only processes the variable's own loads, stores
     * and calls. So outside that window the grouping holds exactly the
     * objects of the points-to set. Inside it (an invocation whose receiver
     * variable is the base variable being propagated) the grouping may lack
     * the difference, which the following {@link #onNewPointsToSet} then
     * hands to every invocation on the variable, including the new one;
     * a grouping created inside the window may list those objects twice,
     * which repeats facts but loses none.
     */
    private final Map<CSVar, ReceiverGroups<Type, CSObj>> recvByType = Maps.newMap();

    /**
     * The interned sources of the lambda call edges of each invokedynamic
     * without captured variables, whose edges read no context of the lambda
     * object ({@link #lambdaSource}).
     */
    private final Map<InvokeDynamic, LambdaSource> nonCapturingSources = Maps.newMap();

    /**
     * The interned sources of the lambda call edges of each lambda object
     * whose invokedynamic captures variables ({@link #lambdaSource}).
     */
    private final Map<CSObj, LambdaSource> capturingSources = Maps.newMap();

    /**
     * Map from each receiver variable of {@link #invoInfos} to the targets
     * of its invocations, with per target the slots of the variable's
     * grouping in {@link #recvByType} (known slots) and of the grouping of
     * the new points-to set being handled (delta slots) whose type may
     * dispatch the target. Created with the variable's grouping; a target
     * gets its known slots at the first invocation of the target on the
     * variable ({@link #groupKnownByCallee}), and the slots of each later
     * type from {@link #matchTargets}.
     */
    private final Map<CSVar, ReceiverTargets> targetsByVar = Maps.newMap();

    /**
     * The class {@code java.lang.Object}: every receiver class is its
     * subclass, so its methods are candidates for every receiver type.
     */
    private JClass objectClass;

    /**
     * Number of the new points-to set being handled by
     * {@link #onNewPointsToSet}; tags the delta slots of
     * {@link #targetsByVar}.
     */
    private long event;

    /**
     * Number of dispatches of a receiver type for a target while grouping
     * receivers by callee (the groupings' {@link ReceiverGroups.Visitor#enter}
     * calls), without those of the verify mode.
     */
    private long enterCalls;

    /**
     * Number of dispatches the same groupings would make by dispatching on
     * every receiver type of the grouping, for comparison with
     * {@link #enterCalls}.
     */
    private long enterFullScan;

    /**
     * System property that turns on {@link GroupingVerifier}.
     */
    private static final String VERIFY_PROPERTY = "spd.lambda.verify";

    /**
     * The verifier of {@link #addLambdaCallEdges}, or null when the verify
     * mode is off.
     */
    @Nullable
    private GroupingVerifier verifier;

    private static final Logger logger = LoggerFactory.getLogger(LambdaAnalysis.class);

    /**
     * The measurement counters, or null unless the pointer analysis keeps
     * counters ({@link DefaultSolver#countersEnabled}); logged once, at the
     * first of {@link #onRelease} and {@link #onFinish}.
     */
    @Nullable
    private LambdaCounters counters;

    /**
     * @return whether {@code obj} is a lambda functional object that this
     * analysis creates at a lambda meta factory call.
     */
    public static boolean isLambdaObj(Obj obj) {
        return obj instanceof MockObj mock && mock.getDescriptor() == LAMBDA_DESC;
    }

    @Override
    public void setSolver(Solver solver) {
        this.solver = solver;
        this.heapModel = solver.getHeapModel();
        this.selector = solver.getContextSelector();
        this.hierarchy = solver.getHierarchy();
        this.csManager = solver.getCSManager();
        this.callSiteFreeContexts = selector.isInstanceContextCallSiteFree();
        this.objectClass = Objects.requireNonNull(hierarchy.getJREClass(ClassNames.OBJECT),
                "no class " + ClassNames.OBJECT);
        this.capturedHeapContext = isCapturedHeapContext(
                solver.getOptions().getString(HEAP_CONTEXT_OPTION));
        if (Boolean.getBoolean(VERIFY_PROPERTY)) {
            boolean noTimeLimit = solver.getOptions().getInt("time-limit") < 0;
            verifier = new GroupingVerifier(noTimeLimit);
        }
        counters = DefaultSolver.countersEnabled(solver.getOptions())
                ? new LambdaCounters() : null;
    }

    /**
     * @return whether {@code option}, the value of
     * {@link #HEAP_CONTEXT_OPTION}, selects the captured-arguments context.
     * @throws IllegalArgumentException if {@code option} is neither
     *                                  {@code method} nor {@code captured}
     */
    private static boolean isCapturedHeapContext(String option) {
        return switch (option) {
            case "method" -> false;
            case "captured" -> true;
            default -> throw new IllegalArgumentException(
                    "Illegal " + HEAP_CONTEXT_OPTION + " option: " + option);
        };
    }

    @Override
    public void onNewStmt(Stmt stmt, JMethod container) {
        if (stmt instanceof Invoke invoke &&
                invoke.isDynamic() &&
                isLambdaMetaFactory(invoke)) {
            InvokeDynamic indy = (InvokeDynamic) invoke.getInvokeExp();
            Type type = indy.getMethodType().getReturnType();
            // record lambda meta factories of new reachable methods
            lambdaObjs.put(container,
                    heapModel.getMockObj(LAMBDA_DESC, invoke, type, container));
        }
    }

    static boolean isLambdaMetaFactory(Invoke invoke) {
        // Declaring class of bootstrap method reference may be phantom
        // (looks like an issue of current (soot-based) front end),
        // thus we use resolveNullable() to avoid exception.
        // TODO: change to resolve() after using new front end
        JMethod bsm = ((InvokeDynamic) invoke.getInvokeExp())
                .getBootstrapMethodRef()
                .resolveNullable();
        if (bsm != null) {
            String bsmSig = bsm.getSignature();
            return bsmSig.equals(Signatures.LAMBDA_METAFACTORY) ||
                    bsmSig.equals(Signatures.LAMBDA_ALTMETAFACTORY);
        } else {
            return false;
        }
    }

    @Override
    public void onNewCSMethod(CSMethod csMethod) {
        JMethod method = csMethod.getMethod();
        Context context = csMethod.getContext();
        lambdaObjs.get(method).forEach(lambdaObj -> {
            // propagate lambda functional objects
            Invoke invoke = (Invoke) lambdaObj.getAllocation();
            Var ret = invoke.getResult();
            assert ret != null;
            // here we use full method context as the heap context of
            // lambda object, so that it can be directly used to obtain
            // context-sensitive captured values later. With the option
            // captured, a lambda without captured variables, which reads
            // nothing under that context, gets the empty heap context.
            Context heapContext = capturedHeapContext
                    ? capturedArgsContext((InvokeDynamic) invoke.getInvokeExp(), context)
                    : context;
            solver.addVarPointsTo(context, ret, heapContext, lambdaObj);
        });
    }

    @Override
    public void onUnresolvedCall(CSObj recv, Context context, Invoke invoke) {
        if (!CSObjs.hasDescriptor(recv, LAMBDA_DESC)) {
            return;
        }
        MockObj lambdaObj = (MockObj) recv.getObject();
        Invoke indyInvoke = (Invoke) lambdaObj.getAllocation();
        InvokeDynamic indy = (InvokeDynamic) indyInvoke.getInvokeExp();
        if (!indy.getMethodName().equals(invoke.getMethodRef().getName())) {
            // Use method name to filter out mismatched (caused by imprecision
            // of pointer analysis) lambda objects and actual invocation sites.
            // TODO: use more information to filter out mismatches?
            return;
        }
        if (counters != null) {
            counters.startEvent();
        }
        LambdaSource source = lambdaSource(recv, indy);
        CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
        MethodHandle mh = getMethodHandle(indy);
        final MethodRef targetRef = mh.getMethodRef();

        switch (mh.getKind()) {
            case REF_newInvokeSpecial -> { // targetRef is constructor
                ClassType type = targetRef.getDeclaringClass().getType();
                // Create mock object (if absent) which represents
                // the newly-allocated object. Note that here we use the
                // *invokedynamic* to represent the *allocation site*,
                // instead of the actual invocation site of the constructor.
                Obj newObj = heapModel.getMockObj(LAMBDA_NEW_DESC,
                        indyInvoke, type, indyInvoke.getContainer());
                // pass the mock object to result variable (if present)
                // TODO: double-check if the heap context is proper
                CSObj csNewObj = csManager.getCSObj(context, newObj);
                Var result = invoke.getResult();
                if (result != null) {
                    solver.addVarPointsTo(context, result, csNewObj);
                }
                // add call edge to constructor
                addLambdaCallEdge(csCallSite, csNewObj, targetRef, source);
            }
            case REF_invokeInterface, REF_invokeVirtual, REF_invokeSpecial -> {
                // targetRef is instance method
                List<Var> capturedArgs = indy.getArgs();
                List<Var> actualArgs = invoke.getInvokeExp().getArgs();
                // Obtain receiver variable and context
                Var recvVar;
                Context recvCtx;
                if (!capturedArgs.isEmpty()) {
                    // if captured arguments are not empty, then the first one
                    // must be the receiver object for targetRef
                    recvVar = capturedArgs.get(0);
                    recvCtx = source.getContext();
                } else {
                    // otherwise, the first actual argument is the receiver
                    recvVar = actualArgs.get(0);
                    recvCtx = context;
                }
                CSVar csRecvVar = csManager.getCSVar(recvCtx, recvVar);
                PointsToSet recvObjs = solver.getPointsToSetOf(csRecvVar);
                ReceiverGroups<Type, CSObj> recvObjsByType = recvByType.computeIfAbsent(
                        csRecvVar, v -> groupByType(recvObjs));
                ReceiverTargets targets = targetsByVar.computeIfAbsent(
                        csRecvVar, v -> new ReceiverTargets());
                if (verifier != null) {
                    verifier.setPartial(csRecvVar == baseVarOf(context, invoke));
                }
                InstanceInvoInfo info = new InstanceInvoInfo(csCallSite, source,
                        targetRef, argsToStatic(csCallSite, indy),
                        argsToInstance(csCallSite, indy));
                addLambdaCallEdges(info, recvObjs, groupKnownByCallee(
                        csCallSite, targetRef, recvObjsByType, targets));
                // New objects may reach csRecvVar later, thus we store it
                // together with information about the related Lambda invocation.
                invoInfos.put(csRecvVar, info);
            }
            case REF_invokeStatic -> // targetRef is static method
                    addLambdaCallEdge(csCallSite, null, targetRef, source);
            default -> throw new AnalysisException(mh.getKind() + " is not supported");
        }
    }

    /**
     * @return the context under which the lambda call edges of {@code indy}
     * read its captured variables: the lambda object's heap context
     * {@code lambdaObjCtx} (the context of the method that created it), or
     * the empty context when {@code indy} captures no variable. The captured
     * variables are the only facts read under this context
     * ({@link #onNewCallEdge}), and it is part of a lambda call edge's
     * identity, so without captures the edges of one call site and callee
     * no longer differ per context of the creating method.
     */
    private Context capturedArgsContext(InvokeDynamic indy, Context lambdaObjCtx) {
        return indy.getArgs().isEmpty() ? selector.getEmptyContext() : lambdaObjCtx;
    }

    /**
     * @return the interned source of the lambda call edges on
     * {@code lambdaObj}, created by {@code indy}: its invokedynamic and
     * {@link #capturedArgsContext}. Equal sources are the same object, one
     * per invokedynamic without captured variables and one per lambda
     * object otherwise (an invokedynamic creates one lambda object per
     * heap context), so the call edges share them.
     */
    private LambdaSource lambdaSource(CSObj lambdaObj, InvokeDynamic indy) {
        if (indy.getArgs().isEmpty()) {
            return nonCapturingSources.computeIfAbsent(indy, i -> new LambdaSource(
                    i, capturedArgsContext(i, lambdaObj.getContext())));
        }
        return capturingSources.computeIfAbsent(lambdaObj, o -> new LambdaSource(
                indy, capturedArgsContext(indy, o.getContext())));
    }

    /**
     * @return the MethodHandle to the target method from invokedynamic.
     */
    private static MethodHandle getMethodHandle(InvokeDynamic indy) {
        return (MethodHandle) indy.getBootstrapArgs().get(1);
    }

    /**
     * @return the context-sensitive base variable of {@code invoke}, or null
     * if {@code invoke} is not an instance invocation. Used by the verify
     * mode only.
     */
    @Nullable
    private CSVar baseVarOf(Context context, Invoke invoke) {
        return invoke.getInvokeExp() instanceof InvokeInstanceExp exp
                ? csManager.getCSVar(context, exp.getBase())
                : null;
    }

    /**
     * Whether the arguments transferred by this edge fit into {@code callee}'s
     * parameters, using the same shifts as {@link #onNewCallEdge}.
     */
    private static boolean fitsParameterCount(
            CSCallSite csCallSite, InvokeDynamic indy, JMethod callee) {
        return fitsParameterCount(callee, argsToStatic(csCallSite, indy),
                argsToInstance(csCallSite, indy));
    }

    /**
     * {@link #fitsParameterCount(CSCallSite, InvokeDynamic, JMethod)} with
     * the transferred argument counts of the edge's call site and
     * invokedynamic computed in advance.
     */
    private static boolean fitsParameterCount(
            JMethod callee, int argsToStatic, int argsToInstance) {
        if (callee.isAbstract()) {
            return false;
        }
        int transferred = callee.isStatic() || callee.isConstructor()
                ? argsToStatic : argsToInstance;
        return transferred <= callee.getParamCount();
    }

    /**
     * @return the number of arguments an edge transfers into the parameters
     * of a static method or constructor: with no receiver, every captured
     * variable and actual argument is a parameter.
     */
    private static int argsToStatic(CSCallSite csCallSite, InvokeDynamic indy) {
        return indy.getArgs().size()
                + csCallSite.getCallSite().getInvokeExp().getArgCount();
    }

    /**
     * @return the number of arguments an edge transfers into the parameters
     * of an instance method: all but the receiver, which is the first
     * captured variable or, without captures, the first actual argument.
     */
    private static int argsToInstance(CSCallSite csCallSite, InvokeDynamic indy) {
        int captured = indy.getArgs().size();
        int actual = csCallSite.getCallSite().getInvokeExp().getArgCount();
        return captured == 0 ? Math.max(0, actual - 1) : (captured - 1) + actual;
    }

    private void addLambdaCallEdge(
            CSCallSite csCallSite, @Nullable CSObj recvObj, MethodRef targetRef,
            LambdaSource source) {
        JMethod callee;
        Context calleeCtx;
        if (recvObj != null) {
            // recvObj is not null, meaning that callee is instance method
            callee = hierarchy.dispatch(recvObj.getObject().getType(), targetRef);
            if (callee == null) {
                return;
            }
            calleeCtx = selector.selectContext(csCallSite, recvObj, callee);
            // pass receiver object to 'this' variable of callee
            solver.addVarPointsTo(calleeCtx, callee.getIR().getThis(), recvObj);
            if (counters != null) {
                counters.thisUpdate(calleeCtx, callee);
            }
        } else { // otherwise, callee is static method
            callee = targetRef.resolveNullable();
            if (callee == null) {
                // this may happen in special cases, e.g.,
                // when the declaring class of targetRef is phantom class
                return;
            }
            calleeCtx = selector.selectContext(csCallSite, callee);
        }
        if (!fitsParameterCount(csCallSite, source.getIndy(), callee)) {
            // A lambda object can reach a call site that only shares its method
            // name; such a pairing cannot be called, so drop the edge.
            return;
        }
        LambdaCallEdge callEdge = new LambdaCallEdge(csCallSite,
                csManager.getCSMethod(calleeCtx, callee), source);
        if (counters != null) {
            counters.edgeBuilt();
        }
        solver.addCallEdge(callEdge);
    }

    /**
     * @return the objects of {@code objs} grouped by their type, in
     * first-seen order.
     */
    private static ReceiverGroups<Type, CSObj> groupByType(PointsToSet objs) {
        ReceiverGroups<Type, CSObj> byType = new ReceiverGroups<>();
        for (CSObj obj : objs) {
            byType.add(obj.getObject().getType(), obj);
        }
        return byType;
    }

    /**
     * Groups receivers by their context-sensitive callee for a target at a
     * call site, callees in first-seen order: a receiver whose type does not
     * dispatch the target is left out. {@link #addLambdaCallEdges} then adds
     * the same facts as {@link #addLambdaCallEdge} for each receiver object:
     * per callee, one points-to update of the callee's this variable with
     * the whole group, and (if the arguments fit) one call edge, instead of
     * one update and one equal edge per receiver object. The work list
     * merges updates of one pointer and the call graph keeps equal edges
     * once, so the points-to facts and call edges added are the same sets.
     * What may differ is the order of work-list entries and, when a pending
     * work-list entry merges a group with objects it already holds, the
     * internal representation (small set or bit set, hence the iteration
     * order) of the callee's this points-to set, and with the propagation
     * order the order in which objects get their indices. Neither changes
     * the solver's fixpoint, which does not depend on propagation order as
     * long as the plugins are monotone and the time limit is not hit.
     * <p>
     * Dispatch depends only on the receiver's type and the target, so the
     * receivers come grouped by type ({@link ReceiverGroups}) and each type
     * is dispatched once ({@link #enter}). A grouping over some slots of the
     * types sees the same receivers in the same order as one over every
     * type, as long as the slots left out are of types that do not dispatch
     * the target.
     */
    private final class CalleeGrouper
            implements ReceiverGroups.Visitor<Type, CSObj, JMethod> {

        private final CSCallSite csCallSite;

        private final MethodRef targetRef;

        /**
         * Receives the slot of each type that dispatches the target, when
         * the grouping visits every type; otherwise null.
         */
        private final ReceiverTargets.@Nullable SlotList hits;

        /**
         * Whether the dispatches count in {@link #enterCalls} and in the
         * {@link LambdaCounters} (not in the verify mode).
         */
        private final boolean counted;

        /**
         * The caller of the grouping for the {@link LambdaCounters}, one of
         * their {@code PATH_} constants.
         */
        private final int path;

        private final Map<CSMethod, PointsToSet> receiversByCallee = new LinkedHashMap<>();

        private int slot;

        private CalleeGrouper(CSCallSite csCallSite, MethodRef targetRef,
                              ReceiverTargets.@Nullable SlotList hits, boolean counted,
                              int path) {
            this.csCallSite = csCallSite;
            this.targetRef = targetRef;
            this.hits = hits;
            this.counted = counted;
            this.path = path;
        }

        @Override
        @Nullable
        public JMethod enter(Type type) {
            JMethod callee = hierarchy.dispatch(type, targetRef);
            if (counted) {
                ++enterCalls;
                if (counters != null) {
                    counters.enter(path, callee != null);
                }
            }
            if (hits != null) {
                if (callee != null) {
                    hits.addLast(slot);
                }
                ++slot;
            }
            return callee;
        }

        @Override
        public void accept(JMethod callee, CSObj recvObj) {
            Context calleeCtx = selector.selectContext(csCallSite, recvObj, callee);
            receiversByCallee.computeIfAbsent(csManager.getCSMethod(calleeCtx, callee),
                    m -> solver.makePointsToSet()).addObject(recvObj);
        }
    }

    /**
     * @return the receivers of {@code recvByType} (the grouping of a receiver
     * variable's whole points-to set, {@link #recvByType}) grouped by their
     * context-sensitive callee for {@code targetRef} at {@code csCallSite}
     * ({@link CalleeGrouper}). For a target the variable already has, only
     * the target's known slots are dispatched; otherwise every type is, and
     * the slots of the types that dispatch it become its known slots. The
     * dispatches count in the {@link LambdaCounters} under
     * {@link LambdaCounters#PATH_CALL}.
     */
    private Map<CSMethod, PointsToSet> groupKnownByCallee(
            CSCallSite csCallSite, MethodRef targetRef,
            ReceiverGroups<Type, CSObj> recvByType, ReceiverTargets targets) {
        enterFullScan += recvByType.keyCount();
        ReceiverTargets.Target target = targets.get(targetRef);
        CalleeGrouper grouper;
        if (target == null) {
            target = targets.add(targetRef);
            grouper = new CalleeGrouper(csCallSite, targetRef, target.known(), true,
                    LambdaCounters.PATH_CALL);
            recvByType.forEachGroup(grouper);
        } else {
            grouper = new CalleeGrouper(csCallSite, targetRef, null, true,
                    LambdaCounters.PATH_CALL);
            ReceiverTargets.SlotList known = target.known();
            recvByType.forEachGroup(known.slots(), known.count(), grouper);
        }
        if (verifier != null) {
            verifier.checkInversion(csCallSite, targetRef, recvByType,
                    grouper.receiversByCallee);
        }
        return grouper.receiversByCallee;
    }

    /**
     * @return the receivers of {@code ptsByType} (the grouping of the new
     * points-to set of {@link #event}) grouped by their context-sensitive
     * callee for {@code target} at {@code csCallSite}
     * ({@link CalleeGrouper}), dispatching only the target's delta slots
     * ({@link #matchTargets}). {@code path} names the caller for the
     * {@link LambdaCounters}.
     */
    private Map<CSMethod, PointsToSet> groupDeltaByCallee(
            CSCallSite csCallSite, ReceiverTargets.Target target,
            ReceiverGroups<Type, CSObj> ptsByType, int path) {
        enterFullScan += ptsByType.keyCount();
        CalleeGrouper grouper = new CalleeGrouper(csCallSite, target.ref(), null, true, path);
        ptsByType.forEachGroup(target.deltaSlots(), target.deltaCount(event), grouper);
        if (verifier != null) {
            verifier.checkInversion(csCallSite, target.ref(), ptsByType,
                    grouper.receiversByCallee);
        }
        return grouper.receiversByCallee;
    }

    /**
     * Gives each target of {@code targets} its delta slots of {@link #event}
     * in {@code ptsByType}, and its known slots of the types new to the
     * variable's grouping {@code known} (those at {@code knownSize} or
     * later, where {@code ptsByType} was appended): per type, in slot order,
     * the targets declared in the type's class, its superclasses, their
     * superinterfaces or {@code java.lang.Object}, the only declaring
     * classes for which {@link ClassHierarchy#dispatch} may find a method
     * (it requires the receiver class to be a subclass of the target's
     * declaring class).
     */
    private void matchTargets(ReceiverTargets targets, ReceiverGroups<Type, CSObj> ptsByType,
                              ReceiverGroups<Type, CSObj> known, int knownSize) {
        for (int slot = 0; slot < ptsByType.keyCount(); ++slot) {
            Type type = ptsByType.keyAt(slot);
            int knownSlot = known.slotOf(type);
            // the known slots of a target cover the types the variable had
            int newKnownSlot = knownSlot >= knownSize ? knownSlot : -1;
            JClass receiverClass = type instanceof ClassType classType
                    ? classType.getJClass()
                    : type instanceof ArrayType ? objectClass : null;
            for (JClass c = receiverClass; c != null; c = c.getSuperClass()) {
                matchDeclaringClass(targets, c, slot, newKnownSlot);
                for (JClass iface : c.getInterfaces()) {
                    matchInterface(targets, iface, slot, newKnownSlot);
                }
            }
            matchDeclaringClass(targets, objectClass, slot, newKnownSlot);
        }
    }

    private void matchInterface(ReceiverTargets targets, JClass iface,
                                int slot, int newKnownSlot) {
        matchDeclaringClass(targets, iface, slot, newKnownSlot);
        for (JClass superIface : iface.getInterfaces()) {
            matchInterface(targets, superIface, slot, newKnownSlot);
        }
    }

    private void matchDeclaringClass(ReceiverTargets targets, JClass declaringClass,
                                     int slot, int newKnownSlot) {
        ReceiverTargets.Target[] declared = targets.declaredIn(declaringClass);
        if (declared == null) {
            return;
        }
        for (ReceiverTargets.Target target : declared) {
            target.addDelta(event, slot);
            if (newKnownSlot >= 0) {
                target.known().addLast(newKnownSlot);
            }
        }
    }

    /**
     * Adds the facts of {@code receiversByCallee} (a {@link CalleeGrouper}
     * grouping for the call site and target of {@code info})
     * for {@code info}: per callee, in the map's order, the points-to update
     * of the callee's this variable and, if the arguments fit, the call edge.
     * The map and its sets are only read, so one grouping may serve several
     * invocations whose grouping it equals.
     */
    private void addLambdaCallEdges(
            InstanceInvoInfo info, PointsToSet recvObjs,
            Map<CSMethod, PointsToSet> receiversByCallee) {
        CSCallSite csCallSite = info.getCSCallSite();
        MethodRef targetRef = info.getTargetRef();
        InvokeDynamic indy = info.getLambdaIndy();
        if (verifier != null) {
            verifier.checkGrouping(csCallSite, recvObjs, targetRef, indy,
                    receiversByCallee);
        }
        receiversByCallee.forEach((csCallee, receivers) -> {
            JMethod callee = csCallee.getMethod();
            // pass receiver objects to 'this' variable of callee
            solver.addVarPointsTo(csCallee.getContext(),
                    callee.getIR().getThis(), receivers);
            if (counters != null) {
                counters.thisUpdate(csCallee.getContext(), callee);
            }
            if (fitsParameterCount(callee, info.getArgsToStatic(),
                    info.getArgsToInstance())) {
                if (counters != null) {
                    counters.edgeBuilt();
                }
                solver.addCallEdge(new LambdaCallEdge(
                        csCallSite, csCallee, info.getLambdaSource()));
            }
        });
    }

    @Override
    public void onPhaseFinish() {
        if (verifier != null) {
            verifier.checkState("phase end");
        }
    }

    /**
     * Drops the caches that only serve the solve ({@link #lambdaObjs},
     * {@link #invoInfos}, {@link #recvByType}, {@link #targetsByVar} and the
     * interning maps of the edge sources; the edges keep their sources): after
     * the release the solver refuses new methods, points-to sets and call
     * edges, so none of them is read again. The verify mode's finish check,
     * which reads the solver state and the size of {@link #recvByType}, runs
     * first.
     */
    @Override
    public void onRelease() {
        checkFinish();
        logCounters();
        lambdaObjs.clear();
        invoInfos.clear();
        recvByType.clear();
        nonCapturingSources.clear();
        capturingSources.clear();
        targetsByVar.clear();
    }

    @Override
    public void onFinish() {
        checkFinish();
        logCounters();
        recvByType.clear();
        targetsByVar.clear();
    }

    /**
     * Logs the counters once, at the first of {@link #onRelease} and
     * {@link #onFinish}, while {@link #invoInfos} still holds the receiver
     * variables.
     */
    private void logCounters() {
        LambdaCounters c = counters;
        if (c != null) {
            List<Integer> infoCounts = new ArrayList<>();
            invoInfos.forEachSet((var, infos) -> infoCounts.add(infos.size()));
            logger.info("Lambda counters: {}", c.line(infoCounts));
            counters = null;
        }
    }

    /**
     * Runs the verify mode's finish check once, at the first of
     * {@link #onRelease} and {@link #onFinish}.
     */
    private void checkFinish() {
        if (verifier != null) {
            verifier.checkState("finish");
            verifier = null;
        }
    }

    /**
     * Verify mode of {@link #addLambdaCallEdges} (-Dspd.lambda.verify=true).
     * Beside each grouped call, the per-object path of
     * {@link #addLambdaCallEdge} is replayed without side effects: per
     * receiver object it dispatches, selects the callee context and records
     * the fact "receiver in this of the callee" and, if the arguments fit,
     * the edge "call site to callee". (a) Per call, the facts and edges of
     * the per-object path must equal those of the grouped path. (b) Every
     * recorded fact and edge must hold in the solver state whenever the work
     * list is empty (each phase end and the finish), unless a time limit is
     * set (the solver may then stop with a non-empty work list). Any
     * difference throws.
     */
    private final class GroupingVerifier {

        private record ThisFact(CSMethod callee, CSObj recv) {
        }

        private record CallFact(CSCallSite callSite, CSMethod callee) {
        }

        private final boolean stateChecks;

        private final Set<ThisFact> pendingThis = new HashSet<>();

        private final Set<CallFact> pendingCalls = new HashSet<>();

        private long calls;

        private long facts;

        private long checkedFacts;

        /**
         * Whether the next grouped call may lack the difference of the
         * points-to set being propagated (see {@link #recvByType}): its
         * facts must then be a subset of the per-object ones; the missing
         * ones are covered by the state checks. Set right before that call
         * and reset by {@link #checkGrouping}.
         */
        private boolean partial;

        private long partialCalls;

        private long partialMissing;

        private long inversionChecks;

        private GroupingVerifier(boolean stateChecks) {
            this.stateChecks = stateChecks;
        }

        private void setPartial(boolean partial) {
            this.partial = partial;
        }

        private void checkGrouping(
                CSCallSite csCallSite, PointsToSet recvObjs, MethodRef targetRef,
                InvokeDynamic indy, Map<CSMethod, PointsToSet> receiversByCallee) {
            Set<ThisFact> original = new HashSet<>();
            Set<CallFact> originalEdges = new HashSet<>();
            for (CSObj recvObj : recvObjs) {
                JMethod callee = hierarchy.dispatch(recvObj.getObject().getType(), targetRef);
                if (callee == null) {
                    continue;
                }
                Context calleeCtx = selector.selectContext(csCallSite, recvObj, callee);
                CSMethod csCallee = csManager.getCSMethod(calleeCtx, callee);
                original.add(new ThisFact(csCallee, recvObj));
                if (fitsParameterCount(csCallSite, indy, callee)) {
                    originalEdges.add(new CallFact(csCallSite, csCallee));
                }
            }
            Set<ThisFact> grouped = new HashSet<>();
            Set<CallFact> groupedEdges = new HashSet<>();
            receiversByCallee.forEach((csCallee, receivers) -> {
                if (fitsParameterCount(csCallSite, indy, csCallee.getMethod())) {
                    groupedEdges.add(new CallFact(csCallSite, csCallee));
                }
                receivers.forEach(recv -> grouped.add(new ThisFact(csCallee, recv)));
            });
            boolean same = partial
                    ? original.containsAll(grouped) && originalEdges.containsAll(groupedEdges)
                    : original.equals(grouped) && originalEdges.equals(groupedEdges);
            if (!same) {
                throw new AnalysisException("[spd] lambda verify: grouped facts differ at "
                        + csCallSite + " (partial=" + partial + "): per-object "
                        + original.size() + "/" + originalEdges.size() + ", grouped "
                        + grouped.size() + "/" + groupedEdges.size());
            }
            if (partial) {
                ++partialCalls;
                partialMissing += original.size() - grouped.size()
                        + originalEdges.size() - groupedEdges.size();
                partial = false;
            }
            ++calls;
            facts += original.size() + originalEdges.size();
            if (stateChecks) {
                pendingThis.addAll(original);
                pendingCalls.addAll(originalEdges);
            }
            if (Long.bitCount(calls) == 1 && calls >= 1024) {
                System.out.println("[spd] lambda verify progress " + counts());
            }
        }

        /**
         * (c) A grouping that dispatched only some slots of {@code groups}
         * must equal, callees and receivers in the same order, the grouping
         * that dispatches every type of {@code groups}.
         */
        private void checkInversion(
                CSCallSite csCallSite, MethodRef targetRef, ReceiverGroups<Type, CSObj> groups,
                Map<CSMethod, PointsToSet> receiversByCallee) {
            CalleeGrouper everyType = new CalleeGrouper(csCallSite, targetRef, null, false,
                    LambdaCounters.PATH_CALL);
            groups.forEachGroup(everyType);
            if (!orderOf(everyType.receiversByCallee).equals(orderOf(receiversByCallee))) {
                throw new AnalysisException("[spd] lambda verify: grouping of " + targetRef
                        + " at " + csCallSite + " differs from the one over every type: "
                        + everyType.receiversByCallee + " vs " + receiversByCallee);
            }
            ++inversionChecks;
        }

        /**
         * @return per callee in order, the callee followed by its receivers
         * in iteration order.
         */
        private static List<List<Object>> orderOf(Map<CSMethod, PointsToSet> receiversByCallee) {
            List<List<Object>> order = new ArrayList<>(receiversByCallee.size());
            receiversByCallee.forEach((callee, receivers) -> {
                List<Object> entry = new ArrayList<>(1 + receivers.size());
                entry.add(callee);
                receivers.forEach(entry::add);
                order.add(entry);
            });
            return order;
        }

        private void checkState(String when) {
            for (ThisFact f : pendingThis) {
                CSVar thisVar = csManager.getCSVar(f.callee().getContext(),
                        f.callee().getMethod().getIR().getThis());
                if (!solver.getPointsToSetOf(thisVar).contains(f.recv())) {
                    throw new AnalysisException("[spd] lambda verify: " + when + ": "
                            + f.recv() + " missing in this of " + f.callee());
                }
            }
            for (CallFact f : pendingCalls) {
                if (!solver.getCallGraph().getCalleesOf(f.callSite()).contains(f.callee())) {
                    throw new AnalysisException("[spd] lambda verify: " + when + ": edge "
                            + f.callSite() + " -> " + f.callee() + " missing");
                }
            }
            checkedFacts += pendingThis.size() + pendingCalls.size();
            pendingThis.clear();
            pendingCalls.clear();
            System.out.println("[spd] lambda verify " + when + " OK " + counts());
        }

        private String counts() {
            long cachedObjs = 0;
            long cachedTypes = 0;
            for (ReceiverGroups<Type, CSObj> byType : recvByType.values()) {
                cachedTypes += byType.keyCount();
                cachedObjs += byType.objectCount();
            }
            return "calls=" + calls + " facts=" + facts + " partialCalls=" + partialCalls
                    + " partialMissing=" + partialMissing + " stateChecks=" + stateChecks
                    + " checkedFacts=" + checkedFacts + " cachedVars=" + recvByType.size()
                    + " cachedTypes=" + cachedTypes + " cachedObjs=" + cachedObjs
                    + " inversionChecks=" + inversionChecks + " enterCalls=" + enterCalls
                    + " enterFullScan=" + enterFullScan;
        }
    }

    @Override
    public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (edge instanceof LambdaCallEdge lambdaCallEdge) {
            if (counters != null) {
                counters.edgeNew();
            }
            CSCallSite csCallSite = lambdaCallEdge.getCallSite();
            CSMethod csCallee = lambdaCallEdge.getCallee();
            Context calleeContext = csCallee.getContext();
            List<Var> capturedArgs = lambdaCallEdge.getCapturedArgs();
            Context lambdaContext = lambdaCallEdge.getLambdaContext();

            JMethod target = csCallee.getMethod();
            // pass arguments captured at invokedynamic
            int shiftC; // shift of captured arguments
            if (capturedArgs.isEmpty()) {
                shiftC = 0;
            } else if (target.isStatic() || target.isConstructor()) {
                shiftC = 0;
            } else { // target is instance method and there is at least
                // one capture argument, then it must be the receiver object,
                // which has been passed to target's this variable when
                // adding call edge. Thus, we skip it and don't pass it
                // to target's parameters.
                shiftC = 1;
            }
            List<Var> targetParams = target.getIR().getParams();
            int j = 0;
            for (int i = shiftC; i < capturedArgs.size(); ++i, ++j) {
                solver.addPFGEdge(new PointerFlowEdge(
                        FlowKind.PARAMETER_PASSING,
                        csManager.getCSVar(lambdaContext, capturedArgs.get(i)),
                        csManager.getCSVar(calleeContext, targetParams.get(j))),
                        // filter spurious objects caused by imprecise lambda objects
                        targetParams.get(j).getType());
            }
            // pass arguments from actual invocation site
            int shiftA; // shift of actual arguments
            if (capturedArgs.isEmpty() &&
                    !target.isStatic() && !target.isConstructor()) {
                // target is instance method and there is no any captured arguments,
                // then the first argument at actual invocation site must be
                // the receiver object, which has been passed to target's
                // this variable when adding call edge. So we can also skip it.
                shiftA = 1;
            } else {
                shiftA = 0;
            }
            Invoke invoke = csCallSite.getCallSite();
            List<Var> actualArgs = invoke.getInvokeExp().getArgs();
            Context callerContext = csCallSite.getContext();
            for (int i = shiftA; i < actualArgs.size(); ++i, ++j) {
                solver.addPFGEdge(new PointerFlowEdge(
                        FlowKind.PARAMETER_PASSING,
                        csManager.getCSVar(callerContext, actualArgs.get(i)),
                        csManager.getCSVar(calleeContext, targetParams.get(j))),
                        // filter spurious objects caused by imprecise lambda objects
                         targetParams.get(j).getType());
            }
            // pass return value
            Var result = invoke.getResult();
            if (result != null) {
                CSVar csResult = csManager.getCSVar(callerContext, result);
                target.getIR().getReturnVars().forEach(ret -> {
                    CSVar csRet = csManager.getCSVar(calleeContext, ret);
                    solver.addPFGEdge(new PointerFlowEdge(
                            FlowKind.RETURN, csRet, csResult),
                            // filter spurious objects caused by imprecise lambda objects
                            result.getType());
                });
            }
        }
    }

    @Override
    public void onNewPointsToSet(CSVar csVar, PointsToSet pts) {
        Set<InstanceInvoInfo> infos = invoInfos.get(csVar);
        if (infos.isEmpty()) {
            return;
        }
        if (counters != null) {
            counters.startEvent();
        }
        // grouped once per new points-to set, shared by every lambda
        // invocation on this receiver variable, and appended to the
        // variable's cached grouping (present since its first invocation)
        ReceiverGroups<Type, CSObj> ptsByType = groupByType(pts);
        ReceiverGroups<Type, CSObj> cached = Objects.requireNonNull(recvByType.get(csVar),
                "no receiver grouping for a lambda receiver variable");
        ReceiverTargets targets = Objects.requireNonNull(targetsByVar.get(csVar),
                "no targets for a lambda receiver variable");
        int knownSize = cached.keyCount();
        cached.appendAll(ptsByType);
        long thisEvent = ++event;
        matchTargets(targets, ptsByType, cached, knownSize);
        // handle the case of that new objects reach base variable
        // of lambda invocation
        if (callSiteFreeContexts && infos.size() > 1) {
            addSharedLambdaCallEdges(infos, pts, ptsByType, targets);
        } else {
            infos.forEach(info -> addLambdaCallEdges(info, pts, groupDeltaByCallee(
                    info.getCSCallSite(), targetOf(targets, info), ptsByType,
                    LambdaCounters.PATH_NEW_PTS)));
        }
        // the delta slots belong to one event at a time: a nested event
        // would have replaced them before the groupings above read them
        if (event != thisEvent) {
            throw new IllegalStateException("lambda receiver event " + thisEvent
                    + " interrupted by event " + event);
        }
    }

    /**
     * @return the target of {@code info} among {@code targets}, the targets
     * of its receiver variable, which got it with the invocation.
     */
    private static ReceiverTargets.Target targetOf(
            ReceiverTargets targets, InstanceInvoInfo info) {
        return Objects.requireNonNull(targets.get(info.getTargetRef()),
                "no target for a lambda invocation");
    }

    /**
     * The same facts, in the same order, as {@link #addLambdaCallEdges} with
     * a {@link #groupDeltaByCallee} grouping for each of {@code infos} in
     * turn, with one grouping per target method reference instead of one
     * per invocation. A grouping reads the call site
     * only through the callee context, which the selector selects without the
     * call site ({@link #callSiteFreeContexts}), and the dispatch of the
     * target; so the invocations of one target have equal groupings, in equal
     * order. Between two invocations the solver state the grouping reads does
     * not change: the facts of an invocation only enter the work list, and
     * its context-sensitive callees were created by the first grouping.
     */
    private void addSharedLambdaCallEdges(
            Set<InstanceInvoInfo> infos, PointsToSet pts,
            ReceiverGroups<Type, CSObj> ptsByType, ReceiverTargets targets) {
        Map<MethodRef, Map<CSMethod, PointsToSet>> groupingByTarget = new HashMap<>();
        for (InstanceInvoInfo info : infos) {
            Map<CSMethod, PointsToSet> receiversByCallee = groupingByTarget.computeIfAbsent(
                    info.getTargetRef(),
                    targetRef -> groupDeltaByCallee(info.getCSCallSite(),
                            targetOf(targets, info), ptsByType,
                            LambdaCounters.PATH_SHARED));
            addLambdaCallEdges(info, pts, receiversByCallee);
        }
    }
}
