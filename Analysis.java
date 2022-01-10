// This program will plot a CFG for a method using soot [ExceptionalUnitGraph feature].
// Arguements : <ProcessOrTargetDirectory> <MainClass> <TargetClass> <TargetMethod>
//Ref: 1) https://gist.github.com/bdqnghi/9d8d990b29caeb4e5157d7df35e083ce
//     2) https://github.com/soot-oss/soot/wiki/Tutorials

////////////////////////////////////////////////////////////////////////////////
import java.beans.Statement;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

import jas.Pair;

////////////////////////////////////////////////////////////////////////////////

import soot.options.Options;

import soot.Unit;
import soot.UnitPatchingChain;
import soot.Scene;
import soot.Body;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.AddExpr;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.ConditionExpr;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.DivExpr;
import soot.jimple.EqExpr;
import soot.jimple.GeExpr;
import soot.jimple.GotoStmt;
import soot.jimple.GtExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.LeExpr;
import soot.jimple.LtExpr;
import soot.jimple.MulExpr;
import soot.jimple.NeExpr;
import soot.jimple.ParameterRef;
import soot.jimple.RetStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.SubExpr;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JReturnVoidStmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Targets;
import soot.Value;
import soot.ValueBox;

import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;

////////////////////////////////////////////////////////////////////////////////

class UnitVal {
    String className;
    String methodName;
    Unit unit;
    String unitString;

    public UnitVal(String className,
            String methodName,
            Integer lineNo,
            Unit unit) {
        this.className = className;
        this.methodName = methodName;
        this.unit = unit;
        this.unitString = unit.toString();

    }

    public UnitVal(String className,
            String methodName,
            Unit unit) {
        this.className = className;
        this.methodName = methodName;
        this.unit = unit;
        this.unitString = unit.toString();

    }

    public UnitVal(UnitVal uv) {
        this.className = uv.className;
        this.methodName = uv.methodName;
        this.unit = uv.unit;
        this.unitString = uv.unit.toString();
    }

    public static UnitVal resetLineNo(UnitVal uv) {

        UnitVal newUv = new UnitVal(uv);

        return newUv;
    }

    public boolean sameMethod(UnitVal u) {
        return this.methodName.equals(u.methodName);
    }

    public boolean sameClass(UnitVal u) {
        return this.className.equals(u.className);
    }

    @Override
    public String toString() {
        return "(" + this.methodName + "," + this.unit + ")";
    }

    @Override
    public int hashCode() {
        return this.className.hashCode() + this.methodName.hashCode()
                + this.unit.hashCode();
    }

    @Override
    public boolean equals(Object o) {

        UnitVal vC = (UnitVal) o;
        return (this.className.equals(vC.className) &&
                this.methodName.equals(vC.methodName) &&
                this.unitString.equals(vC.unitString));
    }

}

class VarContext {
    String className;
    String methodName; // ""
    String varName;
    Boolean isStatic;

    public VarContext(String cN, String mN, String vN, Boolean isStatic) {
        this.className = cN;
        this.methodName = mN; // ""
        this.varName = vN;
        this.isStatic = isStatic;
    }

    @Override
    public int hashCode() {
        return this.className.hashCode() + this.methodName.hashCode() +
                this.varName.hashCode()
                + this.isStatic.hashCode();
    }

    // public void diff(VarContext vC){

    // }

    public String varName() {
        return this.isStatic ? (this.className + "." + this.varName) : this.varName;
    }

    @Override
    public String toString() {
        return "(" + this.methodName + "," + this.varName + "," + this.isStatic + ")";
    }

    @Override
    public boolean equals(Object o) {

        VarContext vC = (VarContext) o;
        return (this.className.equals(vC.className) &&
                this.methodName.equals(vC.methodName) &&
                this.varName.equals(vC.varName) &&
                this.isStatic.equals(vC.isStatic));
    }

}

class CallString {
    public UnitVal caller;
    public CallString parentCaller;
    public Integer lineNo;

    public CallString(UnitVal uv, CallString parentCaller, Integer lineNo) {
        this.caller = uv;
        this.parentCaller = parentCaller;
        this.lineNo = lineNo;
    }

    public CallString(UnitVal uv) {
        this.caller = uv;
        this.parentCaller = null;
        this.lineNo = 100;
    }

    public CallString(UnitVal uv, Integer lineNo) {
        this.caller = uv;
        this.parentCaller = null;
        this.lineNo = lineNo;
    }

    public CallString(CallString cS) {
        this.caller = cS.caller;
        this.parentCaller = cS.parentCaller;
        this.lineNo = cS.lineNo;
    }

    // public String getCallString() {

    // String lineNo = "in" + String.format("%02d", this.lineNo);
    // return this == null ? "@"
    // : (this.caller.className + "." + this.caller.methodName + "." + lineNo);
    // }

    @Override
    public String toString() {
        return this.caller.toString() + " " + this.lineNo;
    }

    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }

    @Override
    public boolean equals(Object o) {
        CallString vC = (CallString) o;
        return this.toString().equals(vC.toString());
    }
}

public class Analysis extends PAVBase {
    /**
     * ---------------------------- DATA STRUCTURES -----------------------------
     */
    // ? visited -> (ClassName, MethodName,LineNo, Unit) -> Boolean
    private static HashMap<UnitVal, Boolean> visited = new HashMap<>();

    // ? Store all variables
    private static Set<VarContext> variables = new HashSet();
    public static HashMap<UnitVal, HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>>> unitToVarMap = new HashMap<>();
    // Set<Vector:(ClassName, Method, )
    // ClassName -> MethodName -> Set<String>

    private static Set<Pair<String, String>> _methodsScannedForVars = new HashSet();

    // ? Output Data Structures
    private static Set<ResultTuple> analysis_Statements = new HashSet<>();
    private static Set<ResultTuple> analysisIntermediate = new HashSet<>();

    private static Boolean flag = true;

    private static boolean includeForPrint = false;

    // ? Phase 2 : Additional Call and Return Edges
    private static HashMap<UnitVal, Set<UnitVal>> callReturnEdges = new HashMap<>(); // Unamrk Successors
    private static HashMap<UnitVal, Set<UnitVal>> callReturnEdgesReverse = new HashMap<>(); // To Fetch Parent Values
    private static HashMap<UnitVal, UnitVal> callReturnPairs = new HashMap<>();
    // ? UnitVal to Line Map
    private static HashMap<UnitVal, Integer> unitValMap = new HashMap<>();

    /**
     * -----------------------------------------------------------------------------
     */

    /**
     * ----------------------------------HELPER METHODS-----------------------------
     */

    public static void sop(Object o) {
        System.out.println(o);
    }

    protected static UnitPatchingChain getMethodUnits(SootMethod entryMethod) {

        if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {
            Body body = entryMethod.retrieveActiveBody();
            return body.getUnits();
        }
        return null;

    }

    private static void initVisited() {
        for (UnitVal uV : unitValMap.keySet()) {
            visited.put(uV, false);
        }
    }

    protected static void initUnitValLineMap(SootMethod entryMethod) {

        String className = entryMethod.getDeclaringClass().getName();
        _methodsScannedForVars.add(new Pair(className, entryMethod.getName()));

        UnitPatchingChain units = getMethodUnits(entryMethod);
        if (units == null)
            return;

        Body body = entryMethod.retrieveActiveBody();
        int lineNo = 0;
        for (Unit u : body.getUnits()) {
            if (!(u instanceof Stmt)) {
                continue;
            }
            Stmt s = (Stmt) u;
            UnitVal uVal = new UnitVal(className, entryMethod.getName(), 0, u);
            unitValMap.put(uVal, lineNo);

            if (s instanceof InvokeStmt) {

                InvokeExpr inv = ((InvokeStmt) u).getInvokeExpr();
                SootMethod callMethod = inv.getMethod();
                String calleeClass = callMethod.getDeclaringClass().getName();
                String calleeMethod = callMethod.getName();
                Pair<String, String> currentClassMethod = new Pair(calleeClass, calleeMethod);
                if (!_methodsScannedForVars.contains(currentClassMethod)) {
                    initUnitValLineMap(inv.getMethod());
                }
            }
            lineNo++;

        }

    }

    protected static Set<UnitVal> getReturnStatements(SootMethod m) {
        Set<UnitVal> result = new HashSet<>();
        int lineNo = 0;
        for (Unit u : m.retrieveActiveBody().getUnits()) {
            if (!(u instanceof Stmt)) {
                continue;
            }
            if (u instanceof JReturnVoidStmt) {
                result.add(new UnitVal(m.getDeclaringClass().getName(), m.toString(), lineNo, u));
            }
            lineNo++;
        }

        return result;
    }

    protected static void getVariables(SootMethod entryMethod) {
        _methodsScannedForVars.add(new Pair(entryMethod.getDeclaringClass().getName(), entryMethod.getName()));

        UnitPatchingChain units = getMethodUnits(entryMethod);
        if (units == null)
            return;

        Body body = entryMethod.retrieveActiveBody();

        int lineNo = 0;
        for (Unit u : body.getUnits()) {
            if (!(u instanceof Stmt)) {
                continue;
            }
            Stmt s = (Stmt) u;

            String callerClass = entryMethod.getDeclaringClass().getName();
            String callerMethod = entryMethod.getName();
            if (s instanceof InvokeStmt) {

                InvokeExpr inv = ((InvokeStmt) u).getInvokeExpr();
                SootMethod callMethod = inv.getMethod();
                String calleeClass = callMethod.getDeclaringClass().getName();
                String calleeMethod = callMethod.getName();
                Pair<String, String> currentClassMethod = new Pair(calleeClass, calleeMethod);
                if (!_methodsScannedForVars.contains(currentClassMethod)) {
                    getVariables(inv.getMethod());
                }

                // Call Edge

                UnitVal e1_u = new UnitVal(callerClass, callerMethod, lineNo, u);
                Unit e1_vUnit = callMethod.retrieveActiveBody().getUnits().getFirst();

                UnitVal e1_v = new UnitVal(calleeClass, calleeMethod, 0, e1_vUnit);

                // e1_v.lineNo = unitValMap.get(e1_v);
                if (callReturnEdges.get(e1_u) != null) {
                    callReturnEdges.get(e1_u).add(e1_v);
                } else {
                    Set<UnitVal> dest = new HashSet<>();
                    dest.add(e1_v);
                    callReturnEdges.put(e1_u, dest);

                }

                if (callReturnEdgesReverse.get(e1_v) != null) {
                    callReturnEdgesReverse.get(e1_v).add(e1_u);
                } else {
                    Set<UnitVal> dest = new HashSet<>();
                    dest.add(e1_u);
                    callReturnEdgesReverse.put(e1_v, dest);

                }

                // Return Edge

                Unit e2_vUnit = getTargetUnits(entryMethod, u, false).get(0).unit;
                UnitVal e2_v = new UnitVal(callerClass, callerMethod, 0, e2_vUnit);

                Set<UnitVal> e2_uUnits = getReturnStatements(callMethod);
                for (UnitVal e2_u : e2_uUnits) {
                    if (callReturnEdgesReverse.get(e2_v) != null) {
                        callReturnEdgesReverse.get(e2_v).add(e2_u);
                    } else {
                        Set<UnitVal> dest = new HashSet<>();
                        dest.add(e2_u);
                        callReturnEdgesReverse.put(e2_v, dest);

                    }
                    if (callReturnEdges.get(e2_u) != null) {
                        callReturnEdges.get(e2_u).add(e2_v);
                    } else {
                        Set<UnitVal> dest = new HashSet<>();
                        dest.add(e2_v);
                        callReturnEdges.put(e2_u, dest);

                    }

                }
                callReturnPairs.put(e2_v, e1_u);

            } else if (s instanceof AssignStmt) {
                for (ValueBox def : s.getUseAndDefBoxes()) {

                    Value v = def.getValue();

                    VarContext var = new VarContext(callerClass, callerMethod, "", false);

                    if (v instanceof Local) {
                        var.varName = v.toString();
                    }

                    if (v instanceof StaticFieldRef) {

                        StaticFieldRef sFRef = (StaticFieldRef) v;
                        var.varName = sFRef.getField().getName();
                        var.methodName = "";
                        var.isStatic = true;

                    }
                    if (var.varName.trim() != "")
                        variables.add(var);

                }
            }
            lineNo++;

        }

    }

    public static List<UnitVal> getTargetUnits(SootMethod entryMethod, Unit u, boolean includeForeignParents) {
        List<UnitVal> res = new ArrayList<>();
        if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {
            Body body = entryMethod.retrieveActiveBody();
            UnitGraph graph = new ExceptionalUnitGraph(body);
            List<Unit> un = graph.getSuccsOf(u);
            for (Unit _un : un) {
                UnitVal pointU = new UnitVal(entryMethod.getDeclaringClass().getName(), entryMethod.getName(), 0,
                        _un);
                res.add(pointU);
            }
            if (includeForeignParents) {
                UnitVal pointU = new UnitVal(entryMethod.getDeclaringClass().getName(), entryMethod.getName(), 0,
                        u);

                if (callReturnEdges.containsKey(pointU)) {

                    for (UnitVal p : callReturnEdges.get(pointU)) {
                        res.add(p);
                    }

                }
            }

        }
        return res;
    }

    protected static void unMarkSuccessors(HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> _old,
            HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> _newVals, SootMethod m, Unit s) {

        String className = m.getDeclaringClass().getName();
        String methodName = m.getName();
        Set<VarContext> vSet = getMethodVariables(className, methodName);
        List<UnitVal> Successors = getTargetUnits(m, s, true);
        if (!_old.keySet().equals(_newVals.keySet())) {
            for (UnitVal u : Successors) {
                visited.put(u, false);
            }
            return;
        }

        for (VarContext v : vSet) {
            for (CallString cS : _newVals.keySet()) {
                HashMap<VarContext, Pair<Integer, Integer>> old = new HashMap<>(_old.get(cS));
                HashMap<VarContext, Pair<Integer, Integer>> newVals = new HashMap<>(_newVals.get(cS));
                if (old == null || !(newVals.get(v).equals(old.get(v)))) {
                    for (UnitVal u : Successors) {
                        visited.put(u, false);
                    }
                    return;
                }
            }

        }
    }

    public static List<UnitVal> getParentUnits(SootMethod entryMethod, Unit u) {
        List<UnitVal> res = new ArrayList<>();
        if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {
            Body body = entryMethod.retrieveActiveBody();
            UnitGraph graph = new ExceptionalUnitGraph(body);
            List<Unit> un = graph.getPredsOf(u);
            for (Unit _un : un) {
                UnitVal pointU = new UnitVal(entryMethod.getDeclaringClass().getName(), entryMethod.getName(), 0,
                        _un);
                res.add(pointU);
            }

            UnitVal pointU = new UnitVal(entryMethod.getDeclaringClass().getName(), entryMethod.getName(), 0,
                    u);

            if (callReturnEdgesReverse.containsKey(pointU)) {
                for (UnitVal p : callReturnEdgesReverse.get(pointU)) {
                    res.add(p);
                }

            }

        }
        return res;
    }

    private static void writeUnitMapToFile() {

        try {
            FileWriter myWriter = new FileWriter("unitMap.txt");

            for (UnitVal uv : unitToVarMap.keySet()) {
                myWriter.write("Stmt: " + uv.toString());
                myWriter.write("\n");
                for (CallString cs : unitToVarMap.get(uv).keySet()) {
                    if (cs == null) {
                        myWriter.write("CallString: @");

                    } else {
                        myWriter.write("CallString: " + cs.toString());

                    }
                    myWriter.write("\n-------------------------------------");
                    myWriter.write("\n");
                    for (VarContext cV : unitToVarMap.get(uv).get(cs).keySet()) {
                        myWriter.write(cV.varName());
                        myWriter.write(" : ");
                        myWriter.write(unitToVarMap.get(uv).get(cs).get(cV).toString());
                        myWriter.write("\n");
                    }

                }
                myWriter.write("\n");
            }

            myWriter.close();
        } catch (IOException e) {
            System.out.println("An error occurred.");
            e.printStackTrace();
        }

    }

    private static void writeToFile(String filename, Set result, String targetDirectory) {

        try {
            FileWriter myWriter = new FileWriter(targetDirectory + '/' + filename);
            String[] ans = fmtOutputData(result);
            for (String a : ans) {
                myWriter.write(a);
                myWriter.write("\n");
            }

            myWriter.close();
            System.out.println("Successfully wrote to the file.");
        } catch (IOException e) {
            System.out.println("An error occurred.");
            e.printStackTrace();
        }

    }

    private static void writeToFileNew(String filename, String targetDirectory) {

        Set<ResultTuple> result = new HashSet<>();
        try {
            FileWriter myWriter = new FileWriter(targetDirectory + '/' + filename);

            for (UnitVal uv : unitToVarMap.keySet()) {
                Integer lineNo = unitValMap.get(UnitVal.resetLineNo(uv));
                for (CallString cs : unitToVarMap.get(uv).keySet()) {
                    for (VarContext cV : unitToVarMap.get(uv).get(cs).keySet()) {
                        ResultTuple r = new ResultTuple(uv.className + "." + uv.methodName,
                                getPrgPointName(lineNo),
                                cs != null && cs.caller != null
                                        ? cs.caller.className + "." + cs.caller.methodName + "."
                                                + getPrgPointName(unitValMap.get(UnitVal.resetLineNo(cs.caller)))
                                        : "@",
                                cV.varName(),
                                numberToString(unitToVarMap.get(uv).get(cs).get(cV).getO1()),
                                numberToString(unitToVarMap.get(uv).get(cs).get(cV).getO2()));

                        if (!result.contains(r)) {
                            result.add(r);
                        }

                    }

                }

            }

            String[] ans = fmtOutputData(result);

            for (String a : ans) {
                myWriter.write(a);
                myWriter.write("\n");
            }

            myWriter.close();
            System.out.println("Successfully wrote to the file.");
        } catch (IOException e) {
            System.out.println("An error occurred.");
            e.printStackTrace();
        }

    }

    public static void printAnalysis(String className, String methodName, String targetDirectory) {

        writeToFileNew(className + "." + methodName + ".output.txt", targetDirectory);
        writeToFile(className + "." + methodName + ".fulloutput.txt", analysisIntermediate, targetDirectory);

    }

    protected static Set<VarContext> getMethodVariables(String className, String methodName) {
        Set<VarContext> resultSet = new HashSet<>();
        for (VarContext v : variables) {
            if (v.className.equals(className) && (v.isStatic || v.methodName.equals(methodName))) {
                resultSet.add(v);
            }
        }
        return resultSet;
    }

    public static HashMap<VarContext, Pair<Integer, Integer>> initMap(String className,
            String methodName) {
        HashMap<VarContext, Pair<Integer, Integer>> temp = new HashMap<>();
        Set<VarContext> mVars = getMethodVariables(className, methodName);
        for (VarContext v : mVars) {
            temp.put(v, new Pair<>(Integer.MIN_VALUE, Integer.MAX_VALUE));
        }

        return temp;
    }

    protected static String numberToString(Integer x) {
        if (x == Integer.MAX_VALUE)
            return "+inf";
        if (x == Integer.MIN_VALUE)
            return "-inf";
        return x.toString();
    }

    protected static boolean isTrueTargetNode(Unit ifStatement, Stmt childStatement, SootMethod m) {
        JIfStmt _if = (JIfStmt) ifStatement;
        List<UnitVal> targetUnits = getTargetUnits(m, ifStatement, false);
        for (UnitVal p : targetUnits) {
            String mName = p.methodName;
            Unit t = p.unit;

            if (m.getName().equals(mName) && (Stmt) t == childStatement && _if.getTarget() == childStatement) {
                return true;
            }
        }
        return false;
    }

    protected static LatticeE getValue(Value a, HashMap<VarContext, Pair<Integer, Integer>> values, VarContext vC) {
        LatticeE res = new LatticeE();

        if (a instanceof Constant) {
            res.high = Integer.parseInt(a.toString());
            res.low = Integer.parseInt(a.toString());
        } else if (a instanceof CastExpr) {
            Value v = ((CastExpr) a).getOp();
            res.high = Integer.parseInt(v.toString());
            res.low = Integer.parseInt(v.toString());
        } else if (a instanceof Local) {

            res.low = values.get(vC).getO1();
            res.high = values.get(vC).getO2();
        }
        return res;
    }

    protected static char getOperator(BinopExpr expr) {

        if (expr instanceof MulExpr) {
            return '*';
        }
        if (expr instanceof SubExpr) {
            return '-';
        }
        if (expr instanceof DivExpr) {
            return '/';
        }

        return '+';
    }

    public static List<UnitVal> getDifferentParents(List<UnitVal> parents, String methodName, CallString ctx) {

        List<UnitVal> diffParents = new ArrayList<>(parents);
        diffParents = new ArrayList<>(diffParents.stream()
                .filter(p -> !p.methodName.equals(methodName) && unitToVarMap.get(p) != null)
                .collect(Collectors.toList()));

        return diffParents;
    }

    public static List<UnitVal> getSameParents(List<UnitVal> parents, String methodName) {
        List<UnitVal> diffParents = new ArrayList<>(parents);
        diffParents = new ArrayList<>(diffParents.stream()
                .filter(p -> p.methodName.equals(methodName) && unitToVarMap.get(p) != null)
                .collect(Collectors.toList()));

        return diffParents;
    }

    protected static HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> fetchDifferentParentValues(
            List<UnitVal> _parentUnits,
            Unit s,
            SootMethod m, HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> currentValues,
            CallString ctx) {
        HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> contextSensitiveResult = new HashMap<>();

        String className = m.getDeclaringClass().getName();
        String methodName = m.getName();

        HashMap<VarContext, Pair<Integer, Integer>> inheritedValues = new HashMap<>(
                initMap(className, methodName));

        Set<VarContext> vSet = getMethodVariables(className, methodName);
        List<UnitVal> parentUnits = getDifferentParents(_parentUnits, methodName, ctx);
        if (parentUnits != null && parentUnits.size() > 0) {
            UnitVal parentUnit = parentUnits.get(0);
            UnitVal currUnitVal = new UnitVal(className, methodName, 0, s);
            Set<CallString> callStrings = unitToVarMap.get(parentUnit).keySet();
            for (CallString _callString : callStrings) {

                if (callReturnEdges.containsKey(parentUnit)) {
                    for (VarContext vC : vSet) {

                        if (unitToVarMap.get(parentUnit).get(ctx.parentCaller).containsKey(vC))
                            inheritedValues.put(vC,
                                    unitToVarMap.get(parentUnit).get(ctx.parentCaller).get(vC));

                    }
                    contextSensitiveResult.put(new CallString(parentUnit, unitValMap.get(parentUnits.get(0))),
                            inheritedValues); // 8
                }

            }
            for (int i = 1; i < parentUnits.size(); i++) {
                Set<CallString> _callStrings = unitToVarMap.get(parentUnits.get(i)).keySet();
                for (CallString _callString : _callStrings) {
                    if (callReturnEdges.containsKey(parentUnits.get(i))) {

                        inheritedValues
                                .putAll(joinHashMap(inheritedValues,
                                        unitToVarMap.get(parentUnits.get(i)).get(_callString), vSet));
                        contextSensitiveResult.put(
                                new CallString(parentUnits.get(i), unitValMap.get(parentUnits.get(i))),
                                inheritedValues); // 5
                    }
                }

            }
        }

        return contextSensitiveResult;

    }

    protected static HashMap<VarContext, Pair<Integer, Integer>> joinHashMap(
            HashMap<VarContext, Pair<Integer, Integer>> a, HashMap<VarContext, Pair<Integer, Integer>> b,
            Set<VarContext> vSet) {

        HashMap<VarContext, Pair<Integer, Integer>> joinedValues = new HashMap<>(a);
        for (VarContext v : vSet) {
            Pair<Integer, Integer> currVarPair = joinedValues.get(v);
            Pair<Integer, Integer> loopVarPair = b.get(v);

            if (currVarPair == null || loopVarPair == null) {
                continue;
            }

            LatticeE l1 = new LatticeE();
            l1.low = currVarPair.getO1();
            l1.high = currVarPair.getO2();

            LatticeE l2 = new LatticeE();
            l2.low = loopVarPair.getO1();
            l2.high = loopVarPair.getO2();

            LatticeE res = new LatticeE();
            res = l1.join_op(l2);
            joinedValues.put(v, new Pair<>(res.low, res.high));

        }

        return joinedValues;

    }

    protected static HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> fetchParentValues(
            List<UnitVal> _parentUnits,
            Unit s,
            SootMethod m, HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> currentValues,
            CallString ctx) {

        boolean isParentInSameMethod = false;

        String className = m.getDeclaringClass().getName();
        String methodName = m.getName();

        HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> contextSensitiveResult = new HashMap<>();
        HashMap<VarContext, Pair<Integer, Integer>> inheritedValues = new HashMap<>(
                initMap(className, methodName));

        Set<VarContext> vSet = getMethodVariables(className, methodName);
        List<UnitVal> parentUnits = getSameParents(_parentUnits, methodName);
        if (_parentUnits != null && _parentUnits.size() > 0) {
            if (parentUnits != null && parentUnits.size() > 0) {
                UnitVal parentUnit = parentUnits.get(0);
                UnitVal _pU = new UnitVal(parentUnit);

                Set<CallString> callStrings = unitToVarMap.get(parentUnit).keySet();

                for (CallString _callString : callStrings) {

                    if (parentUnit.methodName.equals(m.getName())) {
                        // ? Same Method
                        inheritedValues = new HashMap<>(unitToVarMap.get(parentUnit).get(_callString));
                        isParentInSameMethod = true;

                        if ((Stmt) parentUnit.unit instanceof JIfStmt) {

                            ConditionExpr condExp = (ConditionExpr) ((JIfStmt) parentUnit.unit).getCondition();
                            LatticeE res = new LatticeE();
                            Value l = condExp.getOp1();
                            Value r = condExp.getOp2();

                            VarContext lvalctx = new VarContext(className, methodName, l.toString(), false);

                            if (l instanceof StaticFieldRef) {
                                lvalctx.methodName = "";
                                lvalctx.isStatic = true;
                            }

                            VarContext rvalctx = new VarContext(className, methodName, r.toString(), false);

                            if (r instanceof StaticFieldRef) {
                                rvalctx.methodName = "";
                                rvalctx.isStatic = true;
                            }

                            LatticeE curr1 = getValue(l, inheritedValues, lvalctx);
                            LatticeE curr2 = getValue(r, inheritedValues, rvalctx);

                            if (l.toString().charAt(0) == '$' && r instanceof Local) {

                                res = curr2.tf_condstmt(isTrueTargetNode(parentUnit.unit, (Stmt) s, m), (Stmt) s,
                                        parentUnit,
                                        true, curr1);
                                inheritedValues.put(rvalctx, new Pair<>(res.low, res.high));

                            } else {
                                res = curr1.tf_condstmt(isTrueTargetNode(parentUnit.unit, (Stmt) s, m), (Stmt) s,
                                        parentUnit,
                                        false, curr2);
                                inheritedValues.put(lvalctx, new Pair<>(res.low, res.high));

                            }

                        }

                        Boolean widen_flag = false;
                        UnitVal u = new UnitVal(className, methodName, 0, s);
                        Integer line2 = unitValMap.get(parentUnit);
                        Integer line1 = unitValMap.get(u);
                        if (isParentInSameMethod && s instanceof JIfStmt && line1 != null && line2 != null
                                && line1 < line2) {
                            widen_flag = true;

                        }

                        for (int i = 1; i < parentUnits.size(); i++) {
                            _pU = new UnitVal(parentUnits.get(i));

                            if (unitToVarMap.get(parentUnits.get(i)) == null) {
                                continue;
                            }
                            HashMap<VarContext, Pair<Integer, Integer>> parentUnitMap = new HashMap<>(
                                    unitToVarMap.get(_pU).get(ctx));

                            // ? WIDENING OPERATION
                            for (VarContext v : vSet) {
                                Pair<Integer, Integer> currVarPair = inheritedValues.get(v);

                                LatticeE l1 = new LatticeE();
                                l1.low = currVarPair.getO1();
                                l1.high = currVarPair.getO2();

                                Pair<Integer, Integer> loopVarPair = parentUnitMap.get(v) != null
                                        ? parentUnitMap.get(v)
                                        : new Pair(Integer.MIN_VALUE, Integer.MAX_VALUE);

                                LatticeE l2 = new LatticeE();
                                l2.low = loopVarPair.getO1();
                                l2.high = loopVarPair.getO2();

                                LatticeE res = new LatticeE();
                                if (widen_flag || (line1 < unitValMap.get(parentUnits.get(i)))) {
                                    res = l1.widen_op(l2);
                                    widen_flag = false;
                                } else {

                                    res = l1.join_op(l2);
                                }
                                inheritedValues.put(v, new Pair<>(res.low, res.high));

                            }

                        }

                        contextSensitiveResult.put(_callString, inheritedValues);

                    }

                }

            }
            /// For Different Methods

            contextSensitiveResult.putAll(fetchDifferentParentValues(_parentUnits, s, m, currentValues, ctx));

        } else {

            if (ctx == null)
                contextSensitiveResult.put(null, initMap(className, methodName));
        }
        return contextSensitiveResult;
    }

    protected static void handleDefinitionStatement(Unit s, String className, String methodName,
            List<UnitVal> parentUnits, SootMethod m, CallString ctx) {

        UnitVal u = new UnitVal(className, methodName, 0, s);

        HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> currentValues;
        if (unitToVarMap.get(u) != null) {
            currentValues = new HashMap<>(unitToVarMap.get(u));
        } else {
            currentValues = new HashMap<>();
        }
        Integer lineNo = unitValMap.get(u);

        HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> sensitiveInheritedValues = new HashMap<>(
                fetchParentValues(parentUnits, s, m,
                        currentValues, ctx));

        Set<CallString> callStrings = sensitiveInheritedValues.keySet();

        for (CallString callString : callStrings) {

            HashMap<VarContext, Pair<Integer, Integer>> _inheritedValues = new HashMap<>(
                    sensitiveInheritedValues.get(callString));

            HashMap<VarContext, Pair<Integer, Integer>> inheritedValues = new HashMap<>(_inheritedValues);

            Value lval = ((DefinitionStmt) s).getLeftOp();
            Value rval = ((DefinitionStmt) s).getRightOp();

            VarContext currentVar = new VarContext(className, methodName, lval.toString(), false);

            if (lval instanceof StaticFieldRef) {
                currentVar.methodName = "";
                currentVar.isStatic = true;
                currentVar.varName = ((StaticFieldRef) lval).getField().getName();

            }

            Set<VarContext> vSet = getMethodVariables(className, methodName);

            if (rval.toString().charAt(0) != '@') {

                for (VarContext v : vSet) {

                    ResultTuple e = new ResultTuple(className + "." + methodName, getPrgPointName(lineNo),
                            callString != null && callString.caller != null
                                    ? callString.caller.className + "." + callString.caller.methodName + "."
                                            + getPrgPointName(callString.lineNo)
                                    : "@",
                            v.varName(),
                            numberToString(_inheritedValues.get(v).getO1()),
                            numberToString(_inheritedValues.get(v).getO2()));

                    if (includeForPrint) {
                        analysis_Statements.add(e);
                    } else
                        analysisIntermediate.add(e);

                    if (v.equals(currentVar)) {

                        if (rval instanceof BinopExpr) {

                            Value lsubVal = ((BinopExpr) rval).getOp1(); // i0
                            Value rsubVal = ((BinopExpr) rval).getOp2();
                            VarContext lsubValCtx = new VarContext(className, methodName, lsubVal.toString(), false);

                            if (lsubVal instanceof StaticFieldRef) {
                                lsubValCtx.methodName = "";
                                lsubValCtx.isStatic = true;
                            }
                            VarContext rsubValCtx = new VarContext(className, methodName, rsubVal.toString(), false);

                            if (rsubVal instanceof StaticFieldRef) {
                                rsubValCtx.methodName = "";
                                rsubValCtx.isStatic = true;
                            }
                            LatticeE l1 = getValue(lsubVal, _inheritedValues, lsubValCtx);
                            LatticeE l2 = getValue(rsubVal, _inheritedValues, rsubValCtx);
                            // a= c+d, 2+c,
                            LatticeE res = l1.join_op(l2, getOperator((BinopExpr) rval));
                            inheritedValues.put(currentVar, new Pair<>(res.low, res.high));

                        } else if (rval instanceof Constant) {

                            LatticeE l1 = getValue(rval, _inheritedValues, null);
                            l1 = l1.tf_assignstmt((Stmt) s);
                            inheritedValues.put(currentVar, new Pair<>(l1.low, l1.high));
                        } else if (rval instanceof Local || rval instanceof StaticFieldRef) {
                            VarContext rValCtx = new VarContext(className, methodName, rval.toString(), false);

                            if (rval instanceof StaticFieldRef) {
                                rValCtx.methodName = "";
                                rValCtx.isStatic = true;
                            }
                            LatticeE l1 = getValue(rval, _inheritedValues, rValCtx);

                            l1 = l1.tf_assignstmt((Stmt) s);
                            inheritedValues.put(currentVar, new Pair<>(l1.low, l1.high));
                        } else {
                            LatticeE res = new LatticeE();
                            res = res.tf_assignstmt((Stmt) s);
                            inheritedValues.put(currentVar, new Pair<>(res.low, res.high));

                        }
                    }
                }

            }

            // Update inherited Values in each context
            sensitiveInheritedValues.put(callString, inheritedValues);

        }

        unitToVarMap.put(u, sensitiveInheritedValues);

        unMarkSuccessors(currentValues, sensitiveInheritedValues, m, s);

    }

    protected static void defaultHandler(Unit s, String className, String methodName,
            List<UnitVal> parentUnits, SootMethod m, CallString ctx) {

        UnitVal u = new UnitVal(className, methodName, 0, s);

        HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> currentValues;
        if (unitToVarMap.get(u) != null) {
            currentValues = new HashMap<>(unitToVarMap.get(u));
        } else {
            currentValues = new HashMap<>();
        }
        Integer lineNo = unitValMap.get(u);

        HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> sensitiveInheritedValues = new HashMap<>(
                fetchParentValues(parentUnits, s, m,
                        currentValues, ctx));

        Set<CallString> callStrings = new HashSet<>(sensitiveInheritedValues.keySet());

        Set<VarContext> vSet = getMethodVariables(className, methodName);
        for (CallString callString : callStrings) {

            HashMap<VarContext, Pair<Integer, Integer>> _inheritedValues = new HashMap<>(
                    sensitiveInheritedValues.get(callString));

            HashMap<VarContext, Pair<Integer, Integer>> inheritedValues = new HashMap<>(_inheritedValues);

            for (VarContext v : vSet) {
                LatticeE l1 = new LatticeE();
                // Identity Transfer Function for Return Statement
                l1.low = _inheritedValues.get(v).getO1();
                l1.high = _inheritedValues.get(v).getO2();
                LatticeE res = l1.tf_returnstmt((Stmt) s);

                ResultTuple e = new ResultTuple(className + "." + methodName, getPrgPointName(lineNo),
                        callString != null && callString.caller != null
                                ? callString.caller.className + "." + callString.caller.methodName + "."
                                        + getPrgPointName(callString.lineNo)
                                : "@",
                        v.varName(),
                        numberToString(res.low),
                        numberToString(res.high));

                if (includeForPrint) {
                    analysis_Statements.add(e);
                } else
                    analysisIntermediate.add(e);
            }

            sensitiveInheritedValues.put(ctx, inheritedValues);

        }

        unitToVarMap.put(u, sensitiveInheritedValues);

        unMarkSuccessors(currentValues, sensitiveInheritedValues, m, s);
    }

    protected static void handleStaticInvokeStatement(Unit s, String className,
            String methodName,
            List<UnitVal> parentUnits, SootMethod m, CallString ctx) {

        UnitVal u = new UnitVal(className, methodName, 0, s);

        HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> currentValues;
        if (unitToVarMap.get(u) != null) {
            currentValues = new HashMap<>(unitToVarMap.get(u));
        } else {
            currentValues = new HashMap<>();
        }
        Integer lineNo = unitValMap.get(u);

        HashMap<CallString, HashMap<VarContext, Pair<Integer, Integer>>> sensitiveInheritedValues = new HashMap<>(
                fetchParentValues(parentUnits, s, m,
                        currentValues, ctx));

        Set<CallString> callStrings = sensitiveInheritedValues.keySet();

        Set<VarContext> vSet = getMethodVariables(className, methodName);

        for (CallString callString : callStrings) {
            HashMap<VarContext, Pair<Integer, Integer>> _inheritedValues = new HashMap<>(
                    sensitiveInheritedValues.get(callString));

            HashMap<VarContext, Pair<Integer, Integer>> inheritedValues = new HashMap<>(_inheritedValues);

            for (VarContext v : vSet) {

                LatticeE l1 = new LatticeE();

                l1.low = _inheritedValues.get(v).getO1();
                l1.high = _inheritedValues.get(v).getO2();

                LatticeE res = l1.tf_callstmt((Stmt) s);

                ResultTuple e = new ResultTuple(className + "." + methodName, getPrgPointName(lineNo),
                        callString != null && callString.caller != null
                                ? callString.caller.className + "." + callString.caller.methodName + "."
                                        + getPrgPointName(callString.lineNo)
                                : "@",
                        v.varName(),
                        numberToString(res.low),
                        numberToString(res.high));

                if (includeForPrint) {
                    analysis_Statements.add(e);
                } else
                    analysisIntermediate.add(e);
            }

            sensitiveInheritedValues.put(ctx, inheritedValues);

        }

        unitToVarMap.put(u, sensitiveInheritedValues);

        unMarkSuccessors(currentValues, sensitiveInheritedValues, m, s);

        InvokeExpr inv = ((InvokeStmt) s).getInvokeExpr();

        CallString newCtx = new CallString(u, ctx, lineNo);
        doKildall(className, inv.getMethod().getName(), inv.getMethod(), newCtx);

    }

    private static void doKildall(String className, String methodName, SootMethod entryMethod, CallString ctx) {

        int lineNo = 0;
        flag = false;
        UnitPatchingChain bodyUnits = getMethodUnits(entryMethod);
        if (bodyUnits == null)
            return;
        for (Unit u : bodyUnits) {
            if (!(u instanceof Stmt)) {
                continue;
            }

            Stmt s = (Stmt) u;
            UnitVal uV = new UnitVal(className, methodName, 0, u);

            if (!(visited.get(uV))) {
                flag = true;
                visited.put(uV, true);

                List<UnitVal> parentUnits = getParentUnits(entryMethod, u);
                if (s instanceof DefinitionStmt) {
                    handleDefinitionStatement(u, className, methodName, parentUnits,
                            entryMethod, ctx);
                    lineNo++;
                    continue;
                }
                if (s instanceof InvokeStmt) {
                    handleStaticInvokeStatement(u, className, methodName, parentUnits,
                            entryMethod, ctx);
                    lineNo++;
                    continue;
                }

                defaultHandler(u, className, methodName, parentUnits, entryMethod, ctx);
                lineNo++;

            }

            lineNo++;
        }
    }

    public static void doAnalysis(String className, String methodName, SootMethod entryMethod,
            String targetDirectory) {
        initUnitValLineMap(entryMethod);
        _methodsScannedForVars.clear();
        getVariables(entryMethod);
        if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {
            // LOOP while there exists at least one unvisted node
            initVisited();

            while (flag) {
                doKildall(className, methodName, entryMethod, null);
            }
        }
        writeUnitMapToFile();

        printAnalysis(className, methodName, targetDirectory);

    }

    public static void main(String[] args) {

        String targetDirectory = args[0];
        String mClass = args[1];
        String tClass = args[2];
        String tMethod = args[3];
        boolean methodFound = false;

        List<String> procDir = new ArrayList<String>();
        procDir.add(targetDirectory);

        // Set Soot options
        soot.G.reset();
        Options.v().set_process_dir(procDir);
        // Options.v().set_prepend_classpath(true);
        Options.v().set_src_prec(Options.src_prec_only_class);
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().set_keep_line_number(true);
        Options.v().setPhaseOption("cg.spark", "verbose:false");

        Scene.v().loadNecessaryClasses();

        SootClass entryClass = Scene.v().getSootClassUnsafe(mClass);
        SootMethod entryMethod = entryClass.getMethodByNameUnsafe("main");
        SootClass targetClass = Scene.v().getSootClassUnsafe(tClass);
        SootMethod targetMethod = entryClass.getMethodByNameUnsafe(tMethod);

        Options.v().set_main_class(mClass);
        Scene.v().setEntryPoints(Collections.singletonList(entryMethod));

        // System.out.println (entryClass.getName());
        System.out.println("tclass: " + targetClass);
        System.out.println("tmethod: " + targetMethod);
        System.out.println("tmethodname: " + tMethod);
        Iterator mi = targetClass.getMethods().iterator();
        while (mi.hasNext()) {
            SootMethod sm = (SootMethod) mi.next();
            // System.out.println("method: " + sm);
            if (sm.getName().equals(tMethod)) {
                methodFound = true;
                break;
            }
        }

        if (methodFound) {
            printInfo(targetMethod);
            doAnalysis(targetClass.toString(), tMethod.toString(), targetMethod, targetDirectory);
            /*************************************************************
             * XXX This would be a good place to call the function which performs the
             * Kildalls Analysis
             *************************************************************/
            drawMethodDependenceGraph(targetMethod);
        } else {
            System.out.println("Method not found: " + tMethod);
        }
    }

}
