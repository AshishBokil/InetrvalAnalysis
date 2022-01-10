
import java.util.function.UnaryOperator;

import org.jf.dexlib2.iface.value.StringEncodedValue;

import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AddExpr;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.EqExpr;
import soot.jimple.Expr;
import soot.jimple.GeExpr;
import soot.jimple.GtExpr;
import soot.jimple.LeExpr;
import soot.jimple.LtExpr;
import soot.jimple.NeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ConditionExpr;
import soot.jimple.SubExpr;
import soot.jimple.UnopExpr;
import soot.jimple.internal.JIfStmt;
import soot.jimple.parser.node.AAssignStatement;

// Receiver object of LatticeElement possess the existing dataflow fact at a programpoint.

// Method implementation should not modify the receiver object. A fresh object should be returned.

// The Kildall implementation should not directly refer to IA implementation,
//    and should access the dataflow data only via LatticeElement interface.

interface LatticeElement {

    public LatticeElement join_op(LatticeElement r);
    // represents: "this" JOIN "r"
    // this - the existing dataflow fact
    // r - the incoming dataflow fact

    public LatticeElement widen_op(LatticeElement r);
    // represents: "this" WIDEN "r"
    // this - the existing dataflow fact
    // r - the incoming dataflow fact

    public boolean equals(LatticeElement r);

    public LatticeElement tf_assignstmt(Stmt st);

    public LatticeElement tf_condstmt(boolean b, Stmt st);

    public LatticeElement tf_callstmt(Stmt st);

    public LatticeElement tf_returnstmt(Stmt st);
}

class LatticeE implements LatticeElement {

    public Integer low = Integer.MIN_VALUE;
    public Integer high = Integer.MAX_VALUE;

    public LatticeE join_op(LatticeElement r) {
        return this;
    }

    public static void sop(Object o) {
        System.out.println(o);
    }

    public LatticeE join_op(LatticeE r) {
        LatticeE ans = new LatticeE();

        ans.low = Math.min(this.low, r.low);
        ans.high = Math.max(this.high, r.high);

        return ans;
    }

    public LatticeE join_op(LatticeE r, char operator) {
        LatticeE ans = new LatticeE();
        if (operator == '*') {
            if (!(r.low == Integer.MIN_VALUE || this.low == Integer.MIN_VALUE)) {
                ans.low = r.low * this.low;
            }
            if (!(r.high == Integer.MAX_VALUE || this.high == Integer.MAX_VALUE)) {
                ans.high = r.high * this.high;
            }
            return ans;
        }
        if (operator == '+') {
            // sop("lsubval" + this.low + " " + this.high);
            // sop("rsubval" + r.low + " " + r.high);
            if (!(r.low == Integer.MIN_VALUE || this.low == Integer.MIN_VALUE)) {
                ans.low = r.low + this.low;
            }
            if (!(r.high == Integer.MAX_VALUE || this.high == Integer.MAX_VALUE)) {
                ans.high = r.high + this.high;
            }
            // sop(ans.low + " " + ans.high + "\n");
            return ans;
        }

        if (operator == '-') {
            // sop("lsubval" + this.low + " " + this.high);
            // sop("rsubval" + r.low + " " + r.high);
            if (!(r.low == Integer.MIN_VALUE || this.low == Integer.MIN_VALUE)) {
                ans.low = this.low - r.low;
            }
            if (!(r.high == Integer.MAX_VALUE || this.high == Integer.MAX_VALUE)) {
                ans.high = this.high - r.high;
            }
            // sop(ans.low + " " + ans.high + "\n");
            return ans;
        }

        return ans;
    }

    public LatticeE widen_op(LatticeElement r) {
        return this;
    }

    public LatticeE widen_op(LatticeE r) {
        // sop("widen "+this.low+" "+r.low);
        LatticeE ans = new LatticeE();
        if (r.low < this.low) {
            ans.low = Integer.MIN_VALUE;
        } else {
            ans.low = this.low;
        }
        if (r.high > this.high) {
            ans.high = Integer.MAX_VALUE;
        } else {
            ans.high = this.high;
        }
        return ans;

    }

    public LatticeE tf_callstmt(Stmt st) {
        LatticeE ans = new LatticeE();
        ans.low = this.low;
        ans.high = this.high;
        return ans;
    };

    public LatticeE tf_returnstmt(Stmt st) {
        LatticeE ans = new LatticeE();
        ans.low = this.low;
        ans.high = this.high;
        return ans;
    }

    public boolean equals(LatticeE r) {
        return r.low == this.low && r.high == this.high;
    }

    public boolean equals(LatticeElement r) {
        return false;
    }

    public LatticeE tf_assignstmt(Stmt st) {
        LatticeE res = new LatticeE();
        if (st instanceof AssignStmt) {
            Value rValue = ((AssignStmt) st).getRightOp();
            // if (rValue instanceof BinopExpr) {
            // }

            if (rValue instanceof Constant) {
                // System.out.println(rValue);
                res.high = Integer.parseInt(rValue.toString());
                res.low = Integer.parseInt(rValue.toString());
            } else if (rValue instanceof CastExpr) {
                // sop(((AssignStmt) st).getLeftOp());
                Value v = ((CastExpr) rValue).getOp();
                res.high = Integer.parseInt(v.toString());
                res.low = Integer.parseInt(v.toString());
            }

            else {
                res = this;
                // System.out.println(rValue.toString());
                // sop(Analysis.unitMap);
                // sop(Analysis.unitMap.get((Unit)st).get("$i3 "));
                // res.high= Analysis.unitMap.get(st).get(rValue).getO2();
            }

        }
        return res;
    }

    public LatticeE tf_condstmt(boolean b, Stmt st) {
        return this;
    }

    public LatticeE tf_condstmt(boolean b, Stmt s, UnitVal u, Boolean revert, LatticeE rval) {

        LatticeE l1 = new LatticeE();
        ConditionExpr condExp = (ConditionExpr) (((JIfStmt) u.unit).getCondition());

        if ((b && condExp instanceof EqExpr) || (!b && condExp instanceof NeExpr)) {
            l1.low = rval.low;
            l1.high = rval.high;
        }

        else if ((b && condExp instanceof GeExpr) || (!b && condExp instanceof LtExpr)) {
            if (revert) {
                if (this.low < rval.low) {
                    l1.low = this.low;
                } else {
                    l1.low = rval.low;
                }
                if (this.high > rval.high) {
                    l1.high = rval.high;
                } else {
                    l1.high = this.high;
                }

            } else {

                if (l1.low < rval.low) {
                    l1.low = rval.low;
                }
                if (l1.high < rval.high) {
                    l1.high = rval.high;
                }

            }

        }

        else if ((!b && condExp instanceof GeExpr) || (b && condExp instanceof LtExpr)) {

            if (revert) {
                if (this.low < rval.low) {
                    l1.low = rval.low + 1;
                }
                l1.high = this.high;

            } else {
                l1.low = this.low;
                if (rval.high == Integer.MAX_VALUE) {
                    l1.high = Integer.MAX_VALUE;
                } else if (this.high >= rval.high)
                    l1.high = rval.high - 1;
                else
                    l1.high = this.high;
            }

        }

        else if ((b && condExp instanceof GtExpr) || (!b && condExp instanceof LeExpr)) {
            if (rval.low == Integer.MIN_VALUE) {
                l1.low = Integer.MIN_VALUE;
            } else
                l1.low = rval.low + 1;
            l1.high = this.high;
        }

        else if ((!b && condExp instanceof GtExpr) || (b && condExp instanceof LeExpr)) {
            l1.low = this.low;
            l1.high = rval.high;
        }

        return l1;

    }

}
