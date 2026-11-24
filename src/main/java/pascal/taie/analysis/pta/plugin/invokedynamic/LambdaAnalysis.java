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
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Signatures;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

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
     * System property that turns on {@link GroupingVerifier}.
     */
    private static final String VERIFY_PROPERTY = "spd.lambda.verify";

    /**
     * The verifier of {@link #addLambdaCallEdges}, or null when the verify
     * mode is off.
     */
    @Nullable
    private GroupingVerifier verifier;

    @Override
    public void setSolver(Solver solver) {
        this.solver = solver;
        this.heapModel = solver.getHeapModel();
        this.selector = solver.getContextSelector();
        this.hierarchy = solver.getHierarchy();
        this.csManager = solver.getCSManager();
        if (Boolean.getBoolean(VERIFY_PROPERTY)) {
            boolean noTimeLimit = solver.getOptions().getInt("time-limit") < 0;
            verifier = new GroupingVerifier(noTimeLimit);
        }
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
            // context-sensitive captured values later.
            solver.addVarPointsTo(context, ret, context, lambdaObj);
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
        Context indyCtx = capturedArgsContext(indy, recv.getContext());
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
                addLambdaCallEdge(csCallSite, csNewObj, targetRef, indy, indyCtx);
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
                    recvCtx = indyCtx;
                } else {
                    // otherwise, the first actual argument is the receiver
                    recvVar = actualArgs.get(0);
                    recvCtx = context;
                }
                CSVar csRecvVar = csManager.getCSVar(recvCtx, recvVar);
                PointsToSet recvObjs = solver.getPointsToSetOf(csRecvVar);
                ReceiverGroups<Type, CSObj> recvObjsByType = recvByType.computeIfAbsent(
                        csRecvVar, v -> groupByType(recvObjs));
                if (verifier != null) {
                    verifier.setPartial(csRecvVar == baseVarOf(context, invoke));
                }
                addLambdaCallEdges(csCallSite, recvObjs, recvObjsByType,
                        targetRef, indy, indyCtx);
                // New objects may reach csRecvVar later, thus we store it
                // together with information about the related Lambda invocation.
                invoInfos.put(csRecvVar,
                        new InstanceInvoInfo(csCallSite, indy, indyCtx));
            }
            case REF_invokeStatic -> // targetRef is static method
                    addLambdaCallEdge(csCallSite, null, targetRef, indy, indyCtx);
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
    private boolean fitsParameterCount(
            CSCallSite csCallSite, InvokeDynamic indy, JMethod callee) {
        if (callee.isAbstract()) {
            return false;
        }
        int captured = indy.getArgs().size();
        int actual = csCallSite.getCallSite().getInvokeExp().getArgCount();
        int transferred;
        if (callee.isStatic() || callee.isConstructor()) {
            // No receiver: every captured variable and actual argument is a parameter.
            transferred = captured + actual;
        } else if (captured == 0) {
            // The first actual argument is the receiver.
            transferred = Math.max(0, actual - 1);
        } else {
            // The first captured variable is the receiver.
            transferred = (captured - 1) + actual;
        }
        return transferred <= callee.getParamCount();
    }

    private void addLambdaCallEdge(
            CSCallSite csCallSite, @Nullable CSObj recvObj, MethodRef targetRef,
            InvokeDynamic indy, Context indyCtx) {
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
        } else { // otherwise, callee is static method
            callee = targetRef.resolveNullable();
            if (callee == null) {
                // this may happen in special cases, e.g.,
                // when the declaring class of targetRef is phantom class
                return;
            }
            calleeCtx = selector.selectContext(csCallSite, callee);
        }
        if (!fitsParameterCount(csCallSite, indy, callee)) {
            // A lambda object can reach a call site that only shares its method
            // name; such a pairing cannot be called, so drop the edge.
            return;
        }
        LambdaCallEdge callEdge = new LambdaCallEdge(csCallSite,
                csManager.getCSMethod(calleeCtx, callee), indy, indyCtx);
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
     * Adds the same facts as {@link #addLambdaCallEdge} for each receiver
     * object, with the receivers grouped by their context-sensitive callee
     * first: per callee, one points-to update of the callee's this variable
     * with the whole group, and (if the arguments fit) one call edge, instead
     * of one update and one equal edge per receiver object. The work list
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
     * Dispatch depends only on the receiver's type and {@code targetRef}, so
     * the receivers come grouped by type ({@code recvByType}, the objects of
     * {@code recvObjs}) and each type is dispatched once. {@code recvObjs}
     * itself is read only by the verify mode.
     */
    private void addLambdaCallEdges(
            CSCallSite csCallSite, PointsToSet recvObjs,
            ReceiverGroups<Type, CSObj> recvByType, MethodRef targetRef,
            InvokeDynamic indy, Context indyCtx) {
        Map<CSMethod, PointsToSet> receiversByCallee = new LinkedHashMap<>();
        recvByType.forEachGroup(new ReceiverGroups.Visitor<Type, CSObj, JMethod>() {
            @Override
            @Nullable
            public JMethod enter(Type type) {
                return hierarchy.dispatch(type, targetRef);
            }

            @Override
            public void accept(JMethod callee, CSObj recvObj) {
                Context calleeCtx = selector.selectContext(csCallSite, recvObj, callee);
                receiversByCallee.computeIfAbsent(csManager.getCSMethod(calleeCtx, callee),
                        m -> solver.makePointsToSet()).addObject(recvObj);
            }
        });
        if (verifier != null) {
            verifier.checkGrouping(csCallSite, recvObjs, targetRef, indy,
                    receiversByCallee);
        }
        receiversByCallee.forEach((csCallee, receivers) -> {
            JMethod callee = csCallee.getMethod();
            // pass receiver objects to 'this' variable of callee
            solver.addVarPointsTo(csCallee.getContext(),
                    callee.getIR().getThis(), receivers);
            if (fitsParameterCount(csCallSite, indy, callee)) {
                solver.addCallEdge(new LambdaCallEdge(
                        csCallSite, csCallee, indy, indyCtx));
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
     * {@link #invoInfos}, {@link #recvByType}): after the release the solver
     * refuses new methods, points-to sets and call edges, so none of them is
     * read again. The verify mode's finish check, which reads the solver
     * state and the size of {@link #recvByType}, runs first.
     */
    @Override
    public void onRelease() {
        checkFinish();
        lambdaObjs.clear();
        invoInfos.clear();
        recvByType.clear();
    }

    @Override
    public void onFinish() {
        checkFinish();
        recvByType.clear();
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
                    + " cachedTypes=" + cachedTypes + " cachedObjs=" + cachedObjs;
        }
    }

    @Override
    public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (edge instanceof LambdaCallEdge lambdaCallEdge) {
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
        // grouped once per new points-to set, shared by every lambda
        // invocation on this receiver variable, and appended to the
        // variable's cached grouping (present since its first invocation)
        ReceiverGroups<Type, CSObj> ptsByType = groupByType(pts);
        ReceiverGroups<Type, CSObj> cached = Objects.requireNonNull(recvByType.get(csVar),
                "no receiver grouping for a lambda receiver variable");
        cached.appendAll(ptsByType);
        infos.forEach(info -> {
            // handle the case of that new objects reach base variable
            // of lambda invocation
            InvokeDynamic indy = info.getLambdaIndy();
            MethodRef targetRef = getMethodHandle(indy).getMethodRef();
            addLambdaCallEdges(info.getCSCallSite(), pts, ptsByType,
                    targetRef, indy, info.getLambdaContext());
        });
    }
}
