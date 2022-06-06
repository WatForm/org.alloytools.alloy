package edu.mit.csail.sdg.translator;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;

import java.io.PrintWriter;
import java.util.Map;
import java.util.Set;

public interface SolutionInterface {

    int getBitwidth();

    int max();

    int min();

    int unrolls();

    int getMaxSeq();

    int getMaxTrace();

    int getMinTrace();

    int getLoopState();

    int getTraceLength();

    String getOriginalFilename();

    String getOriginalCommand();

    boolean satisfiable();

    SafeList<Sig> getAllReachableSigs();

    boolean hasConfigs();

    Iterable<ExprVar> getAllSkolems();

    Iterable<ExprVar> getAllAtoms();

    A4TupleSet eval(Sig sig);

    A4TupleSet eval(Sig sig, int state);

    A4TupleSet eval(Sig.Field field);

    A4TupleSet eval(Sig.Field field, int state);

    Object eval(Expr expr) throws Err;

    Object eval(Expr expr, int state) throws Err;

    // [electrum] print particular state, if -1 all
    String toString(int state);

    A4Solution next() throws Err;

    A4Solution fork(int p) throws Err;

    boolean isIncremental();

    Set<Pos> lowLevelCore();

    Pair<Set<Pos>, Set<Pos>> highLevelCore();

    void writeXML(String filename) throws Err;

    void writeXML(A4Reporter rep, String filename, Iterable<Func> macros, Map<String, String> sourceFiles) throws Err;

    void writeXML(PrintWriter writer, Iterable<Func> macros, Map<String, String> sourceFiles) throws Err;

    String format();

    // [electrum] format particular state, if -1 all
    String format(int state);

    String atom2name(Object atom);

    Sig.PrimSig atom2sig(Object atom);

}
