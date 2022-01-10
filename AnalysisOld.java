// This program will plot a CFG for a method using soot [ExceptionalUnitGraph feature].
// Arguements : <ProcessOrTargetDirectory> <MainClass> <TargetClass> <TargetMethod>
//Ref: 1) https://gist.github.com/bdqnghi/9d8d990b29caeb4e5157d7df35e083ce
//     2) https://github.com/soot-oss/soot/wiki/Tutorials

////////////////////////////////////////////////////////////////////////////////
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import jas.Pair;

////////////////////////////////////////////////////////////////////////////////

import soot.options.Options;

import soot.Unit;
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

class CallContext {
    String methodName;
    String lineNo;
    String className;

    public CallContext(String m, String ln, String cN) {
        this.methodName = m;
        this.lineNo = ln;
        this.className = cN;
    }

    public String getContext() {
        if (this.methodName == "@") {
            return "@";
        }
        return this.className + "." + this.methodName + "." + this.lineNo;
    }
}

class UnitVal {
    String className;
    String methodName;
    Integer lineNo;
    Unit unit;
}

public class AnalysisOld extends PAVBase {

    // visited -> (ClassName, MethodName,LineNo, Unit) -> Boolean
    private static HashMap<Pair<String, Unit>, Boolean> visited = new HashMap<Pair<String, Unit>, Boolean>();
    private static Boolean flag = true;

    // MethodUnitMap -> (ClassName,)->()
    public static HashMap<String, HashMap<Unit, HashMap<String, Pair<Integer, Integer>>>> methodUnitMap = new HashMap<>();

    private static HashMap<String, HashMap<Unit, Integer>> methodLineToUnit = new HashMap<>();

    private static Set<ResultTuple> analysis_Statements = new HashSet<>();
    private static Set<ResultTuple> analysisIntermediate = new HashSet<>();
    // methodVars: Method -> VariablesSet
    private static HashMap<String, Set<String>> methodVars = new HashMap<>();
    private static Set<String> staticVars = new HashSet<>();
    private static boolean includeForPrint = false;

    private static Set<String> _methodsScannedForVars = new HashSet<String>();
    private static Set<String> _methodsScannedForParams = new HashSet<String>();
    private static HashMap<Pair<CallContext, Unit>, Set<Pair<CallContext, Unit>>> callReturnEdges = new HashMap<>();
    private static HashMap<Pair<CallContext, Unit>, Set<Pair<CallContext, Unit>>> callReturnEdgesReverse = new HashMap<>();

    protected static Boolean isStaticVariable(Value v) {

        return v instanceof StaticFieldRef;

    }

    protected static void getVariables(SootMethod entryMethod) {
        _methodsScannedForVars.add(entryMethod.getName());
        if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {
            Body body = entryMethod.retrieveActiveBody();

            for (Unit u : body.getUnits()) {
                if (!(u instanceof Stmt)) {
                    continue;
                }

                Stmt s = (Stmt) u;

                if (s instanceof InvokeStmt) {

                    InvokeExpr inv = ((InvokeStmt) u).getInvokeExpr();
                    SootMethod callMethod = inv.getMethod();

                    if (!_methodsScannedForVars.contains(callMethod.getName())) {
                        getVariables(inv.getMethod());
                    }
                } else if (s instanceof AssignStmt) {
                    for (ValueBox def : s.getUseAndDefBoxes()) {

                        Value v = def.getValue();

                        String varName = __.getVarName(entryMethod.getName(), v);

                        if (varName.trim().length() > 0) {
                            if (isStaticVariable(v)) {
                                staticVars.add(varName);
                            } else {
                                if (methodVars.containsKey(entryMethod.getName())) {
                                    methodVars.get(entryMethod.getName()).add(varName);
                                } else {
                                    Set<String> varSet = new HashSet<>();
                                    varSet.add(varName);
                                    methodVars.put(entryMethod.getName(), varSet);
                                }

                            }
                        }

                    }
                }

            }

        }

    }

    protected static void getParameters(SootMethod entryMethod) {
        _methodsScannedForParams.add(entryMethod.getName());

        if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {

            Body body = entryMethod.retrieveActiveBody();

            for (Unit u : body.getUnits()) {
                Stmt s = (Stmt) u;

                if (s instanceof InvokeStmt) {
                    InvokeExpr inv = ((InvokeStmt) s).getInvokeExpr();
                    SootMethod callMethod = inv.getMethod();

                    if (!_methodsScannedForParams.contains(callMethod.getName())) {
                        getParameters(inv.getMethod());
                    }
                } else if (s instanceof DefinitionStmt) {
                    DefinitionStmt stmt = (DefinitionStmt) s;
                    Value rval = stmt.getRightOp();

                    if (rval instanceof ParameterRef) {
                        String varName = "@parameter" + ((ParameterRef) rval).getIndex();
                        // vSet.add(varName);
                    }
                }

            }
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

    public static void printAnalysis(String className, String methodName, String targetDirectory) {

        writeToFile(className + "." + methodName + ".output.txt", analysis_Statements, targetDirectory);
        writeToFile(className + "." + methodName + ".fulloutput.txt", analysisIntermediate, targetDirectory);

    }

    public static HashMap initMap(String m) {
        HashMap<String, Pair<Integer, Integer>> temp = new HashMap<>();
        for (String s : methodVars.get(m)) {
            temp.put(s, new Pair<>(Integer.MIN_VALUE, Integer.MAX_VALUE));
        }
        for (String s : staticVars) {
            temp.put(s, new Pair<>(Integer.MIN_VALUE, Integer.MAX_VALUE));
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

    protected static Integer ValueToInteger(Value x) {
        return Integer.parseInt(x.toString());
    }

    public static List<Pair<String, Unit>> getParentUnits(SootMethod entryMethod, Unit u, Contexy) {
        List<Pair<String, Unit>> res = new ArrayList<>();
        if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {
            Body body = entryMethod.retrieveActiveBody();
            ExceptionalUnitGraph graph = new ExceptionalUnitGraph(body);

            List<Unit> un = graph.getPredsOf(u);
            for (Unit _un : un) {
                res.add(new Pair(entryMethod.getName(), _un));
            }
            if (callReturnEdgesReverse.containsKey(new Pair(entryMethod.getName(), u))) {
                for (Pair<String, Unit> p : callReturnEdgesReverse.get(new Pair(entryMethod.getName(), u))) {
                    res.add(p);
                }
            }

        }
        return res;
    }

    public static List<Pair<String, Unit>> getTargetUnits(SootMethod entryMethod, Unit u) {
        List<Pair<String, Unit>> res = new ArrayList<>();
        if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {
            Body body = entryMethod.retrieveActiveBody();
            UnitGraph graph = new ExceptionalUnitGraph(body);
            List<Unit> un = graph.getSuccsOf(u);
            for (Unit _un : un) {
                res.add(new Pair(entryMethod.getName(), _un));
            }
            if (callReturnEdges.containsKey(new Pair(entryMethod.getName(), u))) {
                for (Pair<String, Unit> p : callReturnEdges.get(new Pair(entryMethod.getName(), u))) {
                    res.add(p);
                }
            }
        }
        return res;
    }

    protected static boolean isTrueTargetNode(Unit ifStatement, Stmt childStatement, SootMethod m) {
        JIfStmt _if = (JIfStmt) ifStatement;
        List<Pair<String, Unit>> targetUnits = getTargetUnits(m, ifStatement);
        for (Pair<String, Unit> p : targetUnits) {
            String mName = p.getO1();
            Unit t = p.getO2();

            if (m.getName().equals(mName) && (Stmt) t == childStatement && _if.getTarget() == childStatement) {
                return true;
            }
        }
        return false;
    }

    protected static Value IfConditionGetLeftOp(ConditionExpr exp) {
        return exp.getOp1();
    }

    protected static Value IfConditionGetRightOp(ConditionExpr exp) {
        return exp.getOp2();
    }

    protected static void parseIfCondition(ConditionExpr exp) {
        if (exp instanceof NeExpr) {
            System.out.println("NE:" + exp.getOp1() + " " + exp + " " + exp.getOp2());
        }
        if (exp instanceof EqExpr) {
            System.out.println(exp.getOp1() + " " + exp + " " + exp.getOp2());
        }
        // TODO: ADD Less than greater than equal to

    }

    protected static LatticeE getValue(Value a, HashMap<String, Pair<Integer, Integer>> temp, String methodName) {
        LatticeE res = new LatticeE();

        if (a instanceof Constant) {
            res.high = Integer.parseInt(a.toString());
            res.low = Integer.parseInt(a.toString());
        } else if (a instanceof CastExpr) {
            Value v = ((CastExpr) a).getOp();
            res.high = Integer.parseInt(v.toString());
            res.low = Integer.parseInt(v.toString());
        } else if (a instanceof Local) {
            res.low = temp.get(__.getVarName(methodName, a)).getO1();
            res.high = temp.get(__.getVarName(methodName, a)).getO2();
        }
        return res;
    }

    static boolean widen_flag = false;

    protected static Set<String> getVSet(String methodName) {
        Set<String> vSet = new HashSet<>(methodVars.get(methodName));

        vSet.addAll(staticVars);
        return vSet;

    }

    // protected static HashMap<Unit, HashMap<String, Pair<Integer, Integer>>>
    // initUnitMap(String methodName) {
    // HashMap<Unit, HashMap<String, Pair<Integer, Integer>>> unitMap = new
    // HashMap<>();
    // Set<String> vSet = getVSet(methodName);
    // f
    // for (String v : vSet) {

    // }
    // }

    protected static HashMap<String, Pair<Integer, Integer>> fetchParentValues(List<Pair<String, Unit>> parentUnits,
            Stmt s,
            SootMethod m) {

        HashMap<String, Pair<Integer, Integer>> temp;
        HashMap<String, Pair<Integer, Integer>> prev;
        HashMap<Unit, Integer> lineToUnit = methodLineToUnit.get(m.getName());
        HashMap<Unit, HashMap<String, Pair<Integer, Integer>>> unitMap = methodUnitMap.get(m.getName());
        Set<String> vSet = getVSet(m.getName());

        if (unitMap == null) {
            unitMap = new HashMap<>();
        }
        if (lineToUnit == null) {
            lineToUnit = new HashMap<>();
        }
        prev = unitMap.get(s);
        sop(s + " " + parentUnits);
        // for (Pair<String, Unit> p : parentUnits) {
        // sop(p.getO2());
        // sop(p.getO2().getJavaSourceStartLineNumber());
        // }
        boolean isParentInSameMethod = true;

        if (parentUnits != null && parentUnits.size() > 0) {
            Unit parentUnit = parentUnits.get(0).getO2();
            temp = new HashMap<>();
            if (unitMap.get(parentUnit) != null) {
                // Parent is in same method
                temp = new HashMap<>(unitMap.get(parentUnit));
                isParentInSameMethod = true;
            } else {
                isParentInSameMethod = false;

                // ? Parent in different method
                // ? Filter only static variables
                temp = new HashMap<>();
                HashMap<String, Pair<Integer, Integer>> crossUnitMap = methodUnitMap.get(parentUnits.get(0).getO1())
                        .get(parentUnit);
                if (crossUnitMap != null) {

                    for (String var : crossUnitMap.keySet()) {
                        if (staticVars.contains(var)) {
                            temp.put(var, crossUnitMap.get(var));
                        }
                    }
                }
                for (String var : vSet) {
                    if (!temp.containsKey(var)) {
                        temp.put(var, new Pair<>(Integer.MIN_VALUE, Integer.MAX_VALUE));
                    }
                }

            }

            if ((Stmt) parentUnits.get(0).getO2() instanceof JIfStmt) {
                ConditionExpr condExp = (ConditionExpr) ((JIfStmt) parentUnit).getCondition();
                LatticeE res = new LatticeE();
                Value l = condExp.getOp1();
                Value r = condExp.getOp2();
                LatticeE curr1 = getValue(l, temp, m.getName());
                LatticeE curr2 = getValue(r, temp, m.getName());

                if (l.toString().charAt(0) == '$' && r instanceof Local) {
                    res = curr2.tf_condstmt(isTrueTargetNode(parentUnit, s, m), s, (JIfStmt) parentUnit, true,
                            m.getName());
                    temp.put(__.getVarName(m.getName(), r), new Pair<>(res.low, res.high));
                } else {
                    res = curr1.tf_condstmt(isTrueTargetNode(parentUnit, s, m), s, (JIfStmt) parentUnit, false,
                            m.getName());
                    temp.put(__.getVarName(m.getName(), l), new Pair<>(res.low, res.high));
                }

            }

            Integer line1 = lineToUnit.get(s);
            Integer line2 = lineToUnit.get(parentUnits.get(0).getO2());
            if (s instanceof JIfStmt && line1 != null && line2 != null && line1 < line2) {
                widen_flag = true;

            }

            for (int i = 1; i < parentUnits.size(); i++) {
                if ((Stmt) parentUnits.get(i).getO2() instanceof JIfStmt) {
                    System.out.println("Child of If statement, branch value " + s.fallsThrough());
                }

                if (unitMap.get(parentUnits.get(i)) != null) {
                    isParentInSameMethod = true;

                    // Parent is in same method
                    temp = new HashMap<>(unitMap.get(parentUnit));
                } else {
                    isParentInSameMethod = false;

                    // ? Parent in different method
                    // ? Filter only static variables
                    temp = new HashMap<>();
                    HashMap<String, Pair<Integer, Integer>> crossUnitMap = methodUnitMap
                            .get(parentUnits.get(0).getO1())
                            .get(parentUnit);
                    if (crossUnitMap == null) {
                        continue;
                    }
                    for (String var : crossUnitMap.keySet()) {
                        if (staticVars.contains(var)) {
                            temp.put(var, crossUnitMap.get(var));
                        }
                    }
                    for (String var : vSet) {
                        if (!temp.containsKey(var)) {
                            temp.put(var, new Pair<>(Integer.MIN_VALUE, Integer.MAX_VALUE));
                        }
                    }

                }
                // ? WIDENING OPERATION
                for (String v : vSet) {

                    if (!isParentInSameMethod) {
                        continue;
                    }
                    Pair<Integer, Integer> currVarPair = temp.get(v) != null ? temp.get(v)
                            : new Pair<>(Integer.MIN_VALUE, Integer.MAX_VALUE);
                    sop(v + " " + temp);
                    LatticeE l1 = new LatticeE();
                    l1.low = currVarPair.getO1();
                    l1.high = currVarPair.getO2();

                    Pair<Integer, Integer> loopVarPair = unitMap.get(parentUnits.get(i)).get(v);

                    LatticeE l2 = new LatticeE();
                    l2.low = loopVarPair.getO1();
                    l2.high = loopVarPair.getO2();

                    LatticeE res = new LatticeE();
                    if (widen_flag || (lineToUnit.get(s) < lineToUnit.get(parentUnits.get(i)))) {
                        res = l1.widen_op(l2);
                        widen_flag = false;
                    } else {
                        res = l1.join_op(l2);
                    }
                    temp.put(v, new Pair<>(res.low, res.high));

                }
            }

        } else {
            temp = initMap(m.getName());
        }

        unMarkSuccessors(prev, temp, m, s);

        return temp;
    }

    protected static void unMarkSuccessors(HashMap<String, Pair<Integer, Integer>> prev,
            HashMap<String, Pair<Integer, Integer>> temp, SootMethod m, Stmt s) {

        Set<String> vSet = getVSet(m.getName());

        for (String v : vSet) {
            if (prev == null || !temp.get(v).equals(prev.get(v))) {
                List<Pair<String, Unit>> Successors = getTargetUnits(m, s);
                for (Pair<String, Unit> u : Successors) {
                    visited.put(new Pair<String, Unit>(u.getO1(), u.getO2()), false);
                }
                break;
            }
        }
    }

    public static void sop(Object o) {
        System.out.println(o);
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

    protected static void handleDefinitionStatement(Stmt s, String className, String methodName, int lineno,
            List<Pair<String, Unit>> parentUnits, SootMethod m, CallContext ctx) {
        HashMap<String, Pair<Integer, Integer>> temp = new HashMap<>();
        temp = fetchParentValues(parentUnits, s, m);
        HashMap<String, Pair<Integer, Integer>> prev;
        HashMap<Unit, HashMap<String, Pair<Integer, Integer>>> unitMap = methodUnitMap.get(m.getName());
        if (unitMap == null) {
            unitMap = new HashMap<>();
        }
        prev = unitMap.get(s);

        Value lval = ((DefinitionStmt) s).getLeftOp();
        Value rval = ((DefinitionStmt) s).getRightOp();
        Set<String> vSet = getVSet(methodName);
        sop(temp);
        if (rval.toString().charAt(0) != '@') {
            for (String v : vSet) {

                if (v.equals(__.getVarName(m.getName(), lval))) {

                    ResultTuple e = new ResultTuple(className + "." + methodName, getPrgPointName(lineno),
                            ctx.getContext(),
                            v,
                            numberToString(temp.get(v).getO1()), numberToString(temp.get(v).getO2()));

                    if (includeForPrint) {
                        analysis_Statements.add(e);
                    } else
                        analysisIntermediate.add(e);

                    if (rval instanceof BinopExpr) {

                        Value lsubVal = ((BinopExpr) rval).getOp1(); // i0
                        Value rsubVal = ((BinopExpr) rval).getOp2();
                        LatticeE l1 = getValue(lsubVal, temp, methodName);
                        LatticeE l2 = getValue(rsubVal, temp, methodName);

                        LatticeE res = l1.join_op(l2, getOperator((BinopExpr) rval));
                        temp.put(v, new Pair<>(res.low, res.high));

                    } else if (rval instanceof Constant || rval instanceof Local) {
                        LatticeE l1 = getValue(rval, temp, methodName);

                        l1 = l1.tf_assignstmt(s);
                        temp.put(v, new Pair<>(l1.low, l1.high));
                    } else {
                        LatticeE res = new LatticeE();

                        res = res.tf_assignstmt(s);
                        temp.put(v, new Pair<>(res.low, res.high));

                    }

                } else {
                    // * No Update Use parent values
                    ResultTuple e = new ResultTuple(className + "." + methodName, getPrgPointName(lineno), callString,
                            v,
                            numberToString(temp.get(v).getO1()), numberToString(temp.get(v).getO2()));
                    if (includeForPrint) {
                        analysis_Statements.add(e);
                    } else
                        analysisIntermediate.add(e);
                }

            }
        } else {
            for (String v : vSet) {
                ResultTuple e = new ResultTuple(className + "." + methodName, getPrgPointName(lineno), callString, v,
                        "-inf",
                        "+inf");
                if (includeForPrint) {
                    analysis_Statements.add(e);
                } else
                    analysisIntermediate.add(e);

                temp.put(v, new Pair<>(Integer.MIN_VALUE, Integer.MAX_VALUE));

            }
        }
        unitMap.put(s, temp);

        unMarkSuccessors(prev, temp, m, s);

        methodUnitMap.put(methodName, unitMap);

    }

    protected static void handleIfStatement(Stmt s, String className, String methodName, int lineno,
            List<Pair<String, Unit>> parentUnits, SootMethod m, CallContext ctx) {

        HashMap<String, Pair<Integer, Integer>> temp = new HashMap<>();
        temp = fetchParentValues(parentUnits, s, m);
        HashMap<String, Pair<Integer, Integer>> prev = new HashMap<>();
        HashMap<Unit, HashMap<String, Pair<Integer, Integer>>> unitMap = methodUnitMap.get(m.getName());

        if (unitMap == null) {
            unitMap = new HashMap<>();
        }
        prev = unitMap.get(s);
        Set<String> vSet = getVSet(methodName);

        for (String v : vSet) {
            ResultTuple e = new ResultTuple(className + "." + methodName, getPrgPointName(lineno), ctx.getContext(), v,
                    numberToString(temp.get(v).getO1()), numberToString(temp.get(v).getO2()));
            if (includeForPrint) {
                analysis_Statements.add(e);
            } else
                analysisIntermediate.add(e);
        }
        unitMap.put(s, temp);
        unMarkSuccessors(prev, temp, m, s);

        methodUnitMap.put(m.getName(), unitMap);

    }

    protected static void handleGotoStatement(Stmt s, String className, String methodName, int lineno,
            List<Pair<String, Unit>> parentUnits, SootMethod m, CallContext ctx) {

        HashMap<String, Pair<Integer, Integer>> temp = new HashMap<>();
        HashMap<String, Pair<Integer, Integer>> prev = new HashMap<>();
        HashMap<Unit, HashMap<String, Pair<Integer, Integer>>> unitMap = methodUnitMap.get(m.getName());

        if (unitMap == null) {
            unitMap = new HashMap<>();
        }
        prev = unitMap.get(s);

        temp = fetchParentValues(parentUnits, s, m);
        Set<String> vSet = getVSet(methodName);

        for (String v : vSet) {
            ResultTuple e = new ResultTuple(className + "." + methodName, getPrgPointName(lineno), ctx.getContext(), v,
                    numberToString(temp.get(v).getO1()), numberToString(temp.get(v).getO2()));
            if (includeForPrint) {
                analysis_Statements.add(e);
            } else
                analysisIntermediate.add(e);
        }
        unitMap.put(s, temp);

        unMarkSuccessors(prev, temp, m, s);

        methodUnitMap.put(m.getName(), unitMap);

    }

    // ? PHASE 2

    protected static void handleStaticInvoke(Stmt s, String className, String methodName, int lineno,
            List<Pair<String, Unit>> parentUnits, SootMethod m, CallContext ctx) {
        HashMap<String, Pair<Integer, Integer>> temp = new HashMap<>();
        HashMap<String, Pair<Integer, Integer>> prev = new HashMap<>();
        HashMap<Unit, HashMap<String, Pair<Integer, Integer>>> unitMap = methodUnitMap.get(m.getName());

        if (unitMap == null) {
            unitMap = new HashMap<>();
        }
        prev = unitMap.get(s);

        temp = fetchParentValues(parentUnits, s, m);
        Set<String> vSet = getVSet(methodName);

        for (String v : vSet) {
            ResultTuple e = new ResultTuple(className + "." + methodName, getPrgPointName(lineno), v, ctx.getContext(),
                    numberToString(temp.get(v).getO1()), numberToString(temp.get(v).getO2()));
            if (includeForPrint) {
                analysis_Statements.add(e);
            } else
                analysisIntermediate.add(e);
        }

        unitMap.put(s, temp);

        unMarkSuccessors(prev, temp, m, s);

        InvokeExpr inv = s.getInvokeExpr();

        doKildall(className + "." + m.getName(), className, inv.getMethod().getName(), inv.getMethod(),
                inv.getMethod().getActiveBody());

        methodUnitMap.put(m.getName(), unitMap);

    }

    protected static void defaultHandler(Stmt s, String className, String methodName, int lineno,
            List<Pair<String, Unit>> parentUnits, SootMethod m, CallContext ctx) {

        HashMap<String, Pair<Integer, Integer>> temp = new HashMap<>();
        temp = fetchParentValues(parentUnits, s, m);
        HashMap<Unit, HashMap<String, Pair<Integer, Integer>>> unitMap = methodUnitMap.get(m.getName());
        Set<String> vSet = getVSet(methodName);

        for (String v : vSet) {
            ResultTuple e = new ResultTuple(className + "." + methodName, getPrgPointName(lineno), v, ctx.getContext(),
                    numberToString(temp.get(v).getO1()), numberToString(temp.get(v).getO2()));
            if (includeForPrint) {
                analysis_Statements.add(e);
            } else
                analysisIntermediate.add(e);
        }
        unitMap.put(s, temp);
        methodUnitMap.put(m.getName(), unitMap);

    }

    private static void initVisited(SootMethod entryMethod) {
        if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {
            Body body = entryMethod.retrieveActiveBody();

            int lineno = 0;
            for (Unit u : body.getUnits()) {
                if (!(u instanceof Stmt)) {
                    continue;
                }
                visited.put(new Pair<>(entryMethod.getName(), u), false);
                if (u instanceof InvokeStmt) {
                    InvokeExpr inv = ((InvokeStmt) u).getInvokeExpr();
                    initVisited(inv.getMethod());
                }
                lineno++;
            }

        }
    }

    private static void initCallAndReturnEdges(SootMethod entryMethod, CallContext ctx) {
        if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {
            Body body = entryMethod.retrieveActiveBody();
            int lineNo = 0;
            for (Unit u : body.getUnits()) {
                if (!(u instanceof Stmt)) {

                    continue;
                }
                if (!(u instanceof InvokeStmt)) {
                    lineNo++;
                    continue;
                }
                InvokeExpr inv = ((InvokeStmt) u).getInvokeExpr();
                SootMethod callMethod = inv.getMethod();
                SootMethod callMethodClass = inv.getClass();
                Unit v = callMethod.retrieveActiveBody().getUnits().getFirst();
                Pair<CallContext, Unit> e1_u = new Pair(ctx, u);

                Pair<CallContext, Unit> e1_v = new Pair(ctx, v);
                if (callReturnEdges.containsKey(e1_u)) {
                    callReturnEdges.get(e1_u).add(e1_v);
                } else {
                    Set<Pair<String, Unit>> s = new HashSet<>();
                    s.add(e1_v);
                    callReturnEdges.put(e1_u, s);
                }

                if (callReturnEdgesReverse.containsKey(e1_v)) {
                    callReturnEdgesReverse.get(e1_v).add(e1_u);
                } else {
                    Set<Pair<CallContext, Unit>> s = new HashSet<>();
                    s.add(e1_u);
                    callReturnEdgesReverse.put(e1_v, s);
                }
                Unit lastC = callMethod.retrieveActiveBody().getUnits().getLast();
                Unit returnP = getTargetUnits(entryMethod, u).get(0).getO2();
                Pair<CallContext, Unit> e2_u = new Pair(ctx, lastC);
                Pair<CallContext, Unit> e2_v = new Pair(ctx, returnP);
                if (callReturnEdges.containsKey(e2_u)) {
                    callReturnEdges.get(e2_u).add(e2_v);
                } else {
                    Set<Pair<CallContext, Unit>> s = new HashSet<>();
                    s.add(e2_v);
                    callReturnEdges.put(e2_u, s);
                }
                if (callReturnEdgesReverse.containsKey(e2_v)) {
                    callReturnEdgesReverse.get(e2_v).add(e2_u);
                } else {
                    Set<Pair<CallContext, Unit>> s = new HashSet<>();
                    s.add(e2_u);
                    callReturnEdgesReverse.put(e2_v, s);
                }
                CallContext ctx2 = new CallContext(entryMethod.getName(), getPrgPointName(lineNo),
                        entryMethod.getDeclaringClass().getName());
                initCallAndReturnEdges(callMethod, ctx2);
                lineNo++;

            }

        }

    }

    public static void initLineToUnitMap(SootMethod entryMethod) {
        HashMap<Unit, Integer> lineToUnit = new HashMap<>();
        if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {
            Body body = entryMethod.retrieveActiveBody();
            // sop(entryMethod);
            int lineno = 0;
            for (Unit u : body.getUnits()) {
                if (!(u instanceof Stmt)) {
                    continue;
                }
                lineToUnit.put(u, lineno);
                if (u instanceof InvokeStmt) {
                    InvokeExpr inv = ((InvokeStmt) u).getInvokeExpr();
                    SootMethod callMethod = inv.getMethod();

                    if (!methodLineToUnit.containsKey(callMethod.getName())) {
                        initLineToUnitMap(inv.getMethod());
                    }
                }
                lineno++;
            }

            methodLineToUnit.put(entryMethod.getName(), lineToUnit);

        }

    }

    private static void doKildall(CallContext ctx, String className, String methodName, SootMethod entryMethod,
            Body body) {

        int lineno = 0;
        flag = false;
        for (Unit u : body.getUnits()) {
            if (!(u instanceof Stmt)) {
                continue;
            }
            sop(methodName + " : " + u);

            Stmt s = (Stmt) u;

            if (!visited.get(new Pair<>(methodName, u))) {
                flag = true;
                visited.put(new Pair<>(methodName, u), true);

                List<Pair<String, Unit>> parentUnits = getParentUnits(entryMethod, u);
                if (s instanceof DefinitionStmt) {
                    handleDefinitionStatement(s, className, methodName, lineno, parentUnits, entryMethod, ctx);
                    lineno++;
                    continue;
                }
                if (s instanceof GotoStmt) {
                    handleGotoStatement(s, className, methodName, lineno, parentUnits, entryMethod, ctx);
                    lineno++;
                    continue;
                }
                if (s instanceof JIfStmt) {
                    handleIfStatement(s, className, methodName, lineno, parentUnits, entryMethod, ctx);
                    lineno++;
                    continue;
                }

                if (s instanceof InvokeStmt) {
                    handleStaticInvoke(s, className, methodName, lineno, parentUnits,
                            entryMethod, ctx);
                    continue;
                }
                defaultHandler(s, className, methodName, lineno, parentUnits, entryMethod, ctx);

            }

            lineno++;
        }
    }

    public static void doAnalysis(String className, String methodName, SootMethod entryMethod,
            String targetDirectory) {
        initLineToUnitMap(entryMethod);
        getVariables(entryMethod);
        CallContext ctx = new CallContext("@", "in00", className);
        initCallAndReturnEdges(entryMethod, ctx);
        // getParameters(entryMethod);
        if (!entryMethod.isPhantom() && entryMethod.isConcrete()) {
            Body body = entryMethod.retrieveActiveBody();
            // LOOP while there exists at least one unvisted node
            initVisited(entryMethod);
            while (flag) {
                doKildall(ctx, className, methodName, entryMethod, body);
            }
            includeForPrint = true;
            initVisited(entryMethod);
            doKildall(ctx, className, methodName, entryMethod, body);
        }

        sop(methodUnitMap);

        // for (String m : methodVars.keySet()) {
        // sop(getVSet(m));
        // }
        // for (Pair<String, Unit> p : callReturnEdges.keySet()) {
        // sop(p + " : " + callReturnEdges.get(p));
        // }

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
