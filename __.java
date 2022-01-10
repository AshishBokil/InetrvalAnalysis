import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.Set;

import jas.Pair;
import soot.Local;
import soot.SootMethod;
import soot.Value;
import soot.jimple.StaticFieldRef;

public final class __ {

    public static void sop(Object o) {
        System.out.println(o);
    }

    public static String getVarName(String m, Value v) {

        String varName = "";

        if (v instanceof Local) {
            varName = m + "." + v.toString();
        }

        // ? PHASE 2 :
        if (v instanceof StaticFieldRef) {
            StaticFieldRef s = (StaticFieldRef) v;
            varName = s.getField().getDeclaringClass().getName() + "." + s.getField().getName();
        }
        // sop(varName);
        return varName;
    }

    public static String numberToString(Integer x) {
        if (x == Integer.MAX_VALUE)
            return "+inf";
        if (x == Integer.MIN_VALUE)
            return "-inf";
        return x.toString();
    }
}
