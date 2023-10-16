package ca.uwaterloo.watform.portus.fuzz;

import ca.uwaterloo.watform.portus.ErrorNoPortusSupport;
import ca.uwaterloo.watform.portus.SortPolicy;
import ca.uwaterloo.watform.portus.SortResolvant;
import ca.uwaterloo.watform.portus.UnivSortPolicy;
import ca.uwaterloo.watform.portus.VarMappingContext;
import ca.uwaterloo.watform.portus.cli.CorrectnessChecker;
import com.code_intelligence.jazzer.api.FuzzedDataProvider;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Env;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.ScopeComputer;
import fortress.inputs.ParserException;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * A Jazzer fuzz test that generates a valid Alloy AST from the fuzz input.
 */
@SuppressWarnings("unused")
public final class ASTFuzzTarget {

    private static class FuzzContext {
        public List<Sig> sigs = new ArrayList<>();
        public List<Func> funcs = new ArrayList<>();
        public Env<String, ContextEntry> vars = new Env<>();

        // These sigs shouldn't be used in generation (like they're private from other modules)
        public List<Sig> privateSigs = new ArrayList<>();
    }

    private static class ContextEntry {
        enum Type { FORMULA, EXPR, INT }

        public final Expr expr;
        public final int arity;
        public final Type type;

        private ContextEntry(Expr expr, int arity, Type type) {
            this.expr = expr;
            this.arity = arity;
            this.type = type;
        }
    }

    public static void fuzzerTestOneInput(FuzzedDataProvider data) {
        FuzzContext context = new FuzzContext();

        // Generate all sigs
        int numSigs = data.consumeInt(0, 4);
        List<Sig.PrimSig> primSigs = new ArrayList<>();
        for (int i = 0; i < numSigs; i++) {
            String sigName = "S_" + makeName(data) + "_" + i; // make them unique
            boolean usePrimSig = primSigs.isEmpty() || data.consumeBoolean();
            if (usePrimSig) {
                Sig.PrimSig sig;
                boolean useParent = !primSigs.isEmpty() && data.consumeBoolean();
                Attr[] attrs = pickAttrs(data);
                if (useParent) {
                    Sig.PrimSig parent = pick(primSigs, data);
                    sig = new Sig.PrimSig(null, sigName, new Pos("x", 1, 1), parent, attrs);
                } else {
                    sig = new Sig.PrimSig(sigName, attrs);
                }
                primSigs.add(sig);
                context.sigs.add(sig);
            } else { // subset sig
                int numParents = data.consumeInt(1, context.sigs.size());
                List<Sig> parents = pickSubset(context.sigs, numParents, data);
                Sig.SubsetSig sig = new Sig.SubsetSig(null, sigName, null, parents);
                context.sigs.add(sig);
            }
        }

        // Apply the ordering module
        for (Sig.PrimSig sig : primSigs) {
            if (data.consumeBoolean()) {
                applyOrderingModule(sig, context);
            }
        }

        // Mock a sort policy just for testing definiteness
        // UnivSortPolicy is sufficient for that purpose
        Command scoperMockCommand = new Command(
                true, 3, 4, 4, ExprVar.make(null, "check"), ExprConstant.TRUE);
        ScopeComputer scoper = ScopeComputer.compute(
                A4Reporter.NOP, new A4Options(), context.sigs, scoperMockCommand).b;
        SortPolicy testSortPolicy = new UnivSortPolicy(context.sigs, scoper);

        // Generate fields for each sig
        for (Sig sig : context.sigs) {
            int numFields = data.consumeInt(0, 5);
            for (int i = 0; i < numFields; i++) {
                String fieldName = "f_" + makeName(data) + "_" + i; // make them unique within a sig
                int boundArity = data.consumeInt(1, 3);

                // TODO: field expr bounds use some special AST nodes, like SOMEOF
                Expr bound = makeExpr(data, boundArity, context);
                // Just ignore anything that isn't definite (according to UnivSortPolicy) for now
                // Empty VarMappingContext is okay because this is the top level
                SortResolvant resolvant = testSortPolicy.getMinimalExprSorts(bound, new VarMappingContext());
                if (!resolvant.isDefinite()) {
                    // just skip this field
                    continue;
                }

                Sig.Field field = sig.addField(fieldName, bound);
                context.vars.put(fieldName, new ContextEntry(field, boundArity + 1, ContextEntry.Type.EXPR));
            }
        }

        // Generate funcs
        int numFuncs = data.consumeInt(0, 10);
        for (int i = 0; i < numFuncs; i++) {
            String funcName = "F_" + makeName(data) + "_" + i; // make them unique

            int numDecls = data.consumeInt(0, 5);
            List<Decl> decls = new ArrayList<>();
            List<String> addedVars = new ArrayList<>();
            for (int j = 0; j < numDecls; j++) {
                int arity = data.consumeInt(1, 3);
                // Use univ to avoid typechecking issues
                Expr bound = tileWithArity(Sig.UNIV, arity);
                int numVars = data.consumeInt(1, 3);
                List<ExprVar> vars = new ArrayList<>();
                for (int k = 0; k < numVars; k++) {
                    ExprVar newVar = ExprVar.make(null, makeName(data));
                    addedVars.add(newVar.label);
                    context.vars.put(newVar.label, new ContextEntry(newVar, arity, ContextEntry.Type.EXPR));
                    vars.add(newVar);
                }
                decls.add(new Decl(null, null, null, null, vars, bound));
            }

            Func func;
            boolean isPred = data.consumeBoolean();
            if (isPred) {
                Expr body = makeFormula(data, context);
                func = new Func(null, null, funcName, decls, null, body);
            } else {
                int arity = data.consumeInt(1, 3);
                Expr body = makeExpr(data, arity, context);
                Expr returnBound = tileWithArity(Sig.UNIV, arity); // avoid typechecking issues
                func = new Func(null, null, funcName, decls, returnBound, body);
            }
            context.funcs.add(func);

            // Remove all the vars we added for the func (in reverse of the order they were added)
            for (int j = addedVars.size() - 1; j >= 0; j--) {
                context.vars.remove(addedVars.get(j));
            }
        }

        // Generate the command
        Expr formula = makeFormula(data, context);
        int bitwidth = data.consumeInt(1, 5); // TODO: probably make bitwidth smaller to avoid stack overflows
        int maxseq = data.consumeInt(0, Math.min(8, Util.max(bitwidth)));
        Command command = new Command(
                data.consumeBoolean(), // is it a check or a run?
                data.consumeInt(-1, 12), // overall scope; -1 = not specified
                bitwidth, // bitwidth; -1 = not specified
                maxseq, // maxseq; -1 = not specified
                ExprVar.make(null, "check"), // command keyword?
                formula);
        A4Options options = new A4Options();

        // Use Kodkod-compatible integer semantics for correctness testing
        options.portusOptions.enableKodkodIntCompatibility = true;

        // Add int, univ only here to avoid returning them when generating expressions
        // to avoid errors about mixing sorts or quantifying over univ
        List<Sig> allSigs = new ArrayList<>(context.sigs);
        allSigs.addAll(context.privateSigs);
        allSigs.add(Sig.UNIV);
        allSigs.add(Sig.SIGINT);
        allSigs.add(Sig.SEQIDX);
        allSigs.add(Sig.STRING);

        // Check correctness and throw if bad
        CorrectnessChecker checker = new CorrectnessChecker();
        CorrectnessChecker.Result result;
        try {
            result = checker.checkCorrectness(allSigs, command, options);
        } catch (ErrorType errorType) {
            // This isn't thrown by Portus but sometimes Kodkod throws type errors.
            // Just ignore them - usually due to too-large arity.
            return;
        }
        if (result.kind != CorrectnessChecker.Result.Kind.OK) {
            if (result.kind == CorrectnessChecker.Result.Kind.EXCEPTION
                && (result.exception instanceof ParserException
                    || result.exception.getCause() instanceof ParserException
                    || result.exception instanceof ErrorNoPortusSupport)) {
                // hack: sometimes Z3 throws ParserException, but it doesn't seem to occur outside of tests,
                // so just get the fuzz tester to continue
                // also ignore errors due to lack of Portus support (not correctness issues)
                // and ignore errors due to relations of too-large arity
                return;
            }
            if (result.kind == CorrectnessChecker.Result.Kind.EXCEPTION) {
                throw new RuntimeException("Oh no! Result: " + result, result.exception);
            } else {
                throw new RuntimeException("Oh no! Result: " + result);
            }
        }
    }

    private static <T> T pick(List<? extends T> ts, FuzzedDataProvider data) {
        return ts.get(data.consumeInt(0, ts.size() - 1));
    }

    private static <T> List<T> pickSubset(List<? extends T> ts, int amount, FuzzedDataProvider data) {
        if (amount < 0 || amount > ts.size()) {
            throw new IllegalArgumentException("Bad subset size");
        }
        // Super inefficient!
        List<? extends T> copy = new ArrayList<>(ts);
        List<T> subset = new ArrayList<>();
        for (int i = 0; i < amount; i++) {
            int idx = data.consumeInt(0, copy.size() - 1);
            subset.add(copy.get(idx));
            copy.remove(idx);
        }
        return subset;
    }

    private static Attr[] pickAttrs(FuzzedDataProvider data) {
        List<Attr> attrs = new ArrayList<>();
        if (data.consumeBoolean()) {
            switch (data.consumeInt(1, 4)) {
                case 1:
                    attrs.add(Attr.ONE);
                    break;
                case 2:
                    attrs.add(Attr.LONE);
                    break;
                case 3:
                    attrs.add(Attr.SOME);
                    break;
                case 4:
                    attrs.add(Attr.ABSTRACT);
                    break;
            }
        }
        return attrs.toArray(new Attr[0]);
    }

    private static void applyOrderingModule(Sig.PrimSig sig, FuzzContext context) {
        String prefix = sig.label + "_ord/";
        Sig.PrimSig ordSig = new Sig.PrimSig(prefix + "Ord", Attr.ONE, Attr.PRIVATE);
        Sig.Field firstField = ordSig.addField("First", sig.setOf());
        Sig.Field nextField = ordSig.addField("Next", sig.product(sig));
        ordSig.addFact(ExprList.makeTOTALORDER(null, null, Arrays.asList(
                sig, ordSig.join(firstField), ordSig.join(nextField))));
        context.privateSigs.add(ordSig);

        // simulate everything from the ordering module
        Decl e = sig.oneOf("e");
        Decl e1 = sig.oneOf("e1");
        Decl e2 = sig.oneOf("e2");
        Decl es = sig.setOf("es");
        Func first = new Func(null, null, prefix + "first", Collections.emptyList(), sig.oneOf(),
                ordSig.join(firstField));
        Func next = new Func(null, null, prefix + "next", Collections.emptyList(), sig.product(sig),
                ordSig.join(nextField));
        Func last = new Func(null, null, prefix + "last", Collections.emptyList(), sig.oneOf(),
                sig.minus(next.call().join(sig)));
        Func prev = new Func(null, null, prefix + "prev", Collections.emptyList(), sig.product(sig),
                ordSig.join(nextField).transpose());
        Func nexts = new Func(null, null, prefix + "nexts", Collections.singletonList(e), sig.setOf(),
                e.get().join(ordSig.join(nextField).closure()));
        Func prevs = new Func(null, null, prefix + "prevs", Collections.singletonList(e), sig.setOf(),
                e.get().join(ordSig.join(nextField).transpose().closure()));
        Func lt = new Func(null, null, prefix + "lt", Arrays.asList(e1, e2), null,
                e1.get().in(prevs.call(e2.get())));
        Func gt = new Func(null, null, prefix + "gt", Arrays.asList(e1, e2), null,
                e1.get().in(nexts.call(e2.get())));
        Func lte = new Func(null, null, prefix + "lte", Arrays.asList(e1, e2), null,
                e1.get().equal(e2.get()).or(lt.call(e1.get(), e2.get())));
        Func gte = new Func(null, null, prefix + "gte", Arrays.asList(e1, e2), null,
                e1.get().equal(e2.get()).or(gt.call(e1.get(), e2.get())));
        Func larger = new Func(null, null, prefix + "larger", Arrays.asList(e1, e2), null,
                lt.call(e1.get(), e2.get()).ite(e2.get(), e1.get()));
        Func smaller = new Func(null, null, prefix + "smaller", Arrays.asList(e1, e2), null,
                lt.call(e1.get(), e2.get()).ite(e1.get(), e2.get()));
        Func max = new Func(null, null, prefix + "max", Collections.singletonList(es), sig.loneOf(),
                es.get().minus(es.get().join(ordSig.join(nextField).transpose().closure())));
        Func min = new Func(null, null, prefix + "min", Collections.singletonList(es), sig.loneOf(),
                es.get().minus(es.get().join(ordSig.join(nextField).closure())));
        context.funcs.addAll(Arrays.asList(first, next, last, prev, nexts, prevs,
                lt, gt, lte, gte, larger, smaller, max, min));
    }

    private static Expr makeFormula(FuzzedDataProvider data, FuzzContext context) {
        switch (data.consumeInt(1, 15)) {
            case 1: {
                // variable
                List<Expr> formulas = context.vars.keySet().stream()
                        .map(name -> context.vars.get(name))
                        .filter(entry -> entry.type == ContextEntry.Type.FORMULA)
                        .map(entry -> entry.expr)
                        .collect(Collectors.toList());
                if (formulas.isEmpty()) {
                    return ExprConstant.TRUE;
                }
                return pick(formulas, data);
            }
            case 2: {
                // ExprBinary with formula
                ExprBinary.Op op = pick(Arrays.asList(
                        ExprBinary.Op.IFF,
                        ExprBinary.Op.IMPLIES), data);
                return op.make(null, null, makeFormula(data, context), makeFormula(data, context));
            }
            case 3: {
                // ExprBinary with expr, any sort
                int arity = data.consumeInt(1, 5);
                ExprBinary.Op op = pick(Arrays.asList(
                        ExprBinary.Op.EQUALS,
                        ExprBinary.Op.NOT_EQUALS,
                        ExprBinary.Op.IN,
                        ExprBinary.Op.NOT_IN), data);
                return op.make(null, null, makeExpr(data, arity, context), makeExpr(data, arity, context));
            }
            case 4: {
                // ExprBinary with expr, int-specific
                ExprBinary.Op op = pick(Arrays.asList(
                        ExprBinary.Op.GT,
                        ExprBinary.Op.GTE,
                        ExprBinary.Op.LT,
                        ExprBinary.Op.LTE,
                        ExprBinary.Op.NOT_GT,
                        ExprBinary.Op.NOT_GTE,
                        ExprBinary.Op.NOT_LT,
                        ExprBinary.Op.NOT_LTE), data);
                return op.make(null, null, makeIntExpr(data, context), makeIntExpr(data, context));
            }
            case 5: {
                // ExprUnary with formula
                ExprUnary.Op op = pick(Arrays.asList(
                        ExprUnary.Op.NOOP,
                        ExprUnary.Op.NOT), data);
                return op.make(null, makeFormula(data, context));
            }
            case 6: {
                // ExprUnary with expr, any sort
                int arity = data.consumeInt(1, 5);
                ExprUnary.Op op = pick(Arrays.asList(
                        ExprUnary.Op.LONE,
                        ExprUnary.Op.ONE,
                        ExprUnary.Op.NO,
                        ExprUnary.Op.SOME), data);
                return op.make(null, makeExpr(data, arity, context));
            }
            case 7: {
                // ExprConstant
                return pick(Arrays.asList(ExprConstant.TRUE, ExprConstant.FALSE), data);
            }
            case 8: {
                // ExprITE
                return makeFormula(data, context).ite(
                        makeFormula(data, context), makeFormula(data, context));
            }
            case 9: {
                // ExprList
                ExprList.Op op = pick(Arrays.asList(
                        ExprList.Op.AND,
                        ExprList.Op.OR), data);
                int length = data.consumeInt(2, 10);
                return ExprList.make(null, null, op, IntStream.range(0, length)
                        .mapToObj(i -> makeFormula(data, context))
                        .collect(Collectors.toList()));
            }
            case 10: {
                // ExprQt
                ExprQt.Op op = pick(Arrays.asList(
                        ExprQt.Op.ALL,
                        ExprQt.Op.SOME,
                        ExprQt.Op.LONE,
                        ExprQt.Op.ONE,
                        ExprQt.Op.NO), data);
                List<String> addedVars = new ArrayList<>();

                int numDecls = data.consumeInt(1, 2);
                List<Decl> decls = new ArrayList<>();
                for (int i = 0; i < numDecls; i++) {
                    Expr expr = makeExpr(data, 1, context); // Portus only supports arity 1 here
                    int numVars = data.consumeInt(1, 2);
                    List<ExprVar> declVars = new ArrayList<>();
                    for (int j = 0; j < numDecls; j++) {
                        ExprVar newVar = ExprVar.make(null, makeName(data), expr.type());
                        declVars.add(newVar);
                        context.vars.put(newVar.label, new ContextEntry(newVar, 1, ContextEntry.Type.EXPR));
                        addedVars.add(newVar.label);
                    }
                    Decl decl = new Decl(null, null, null, null, declVars, expr);
                    decls.add(decl);
                }

                Expr sub = makeFormula(data, context);

                // remove the added vars to recover the context
                for (int i = addedVars.size() - 1; i >= 0; i--) {
                    context.vars.remove(addedVars.get(i));
                }

                return op.make(null, null, decls, sub);
            }
            case 11: {
                // ExprLet with formula
                Expr formula = makeFormula(data, context);
                ExprVar newVar = ExprVar.make(null, makeName(data), formula.type());
                context.vars.put(newVar.label, new ContextEntry(newVar, 1, ContextEntry.Type.FORMULA));
                Expr sub = makeFormula(data, context);
                context.vars.remove(newVar.label);
                return ExprLet.make(null, newVar, formula, sub);
            }
            case 12: {
                // ExprLet with expression
                int arity = data.consumeInt(1, 3);
                Expr expr = makeExpr(data, arity, context);
                ExprVar newVar = ExprVar.make(null, makeName(data), expr.type());
                context.vars.put(newVar.label, new ContextEntry(newVar, arity, ContextEntry.Type.EXPR));
                Expr sub = makeFormula(data, context);
                context.vars.remove(newVar.label);
                return ExprLet.make(null, newVar, expr, sub);
            }
            case 13: {
                // ExprLet with integer expression
                Expr expr = makeIntExpr(data, context);
                ExprVar newVar = ExprVar.make(null, makeName(data), expr.type());
                context.vars.put(newVar.label, new ContextEntry(newVar, 1, ContextEntry.Type.INT));
                Expr sub = makeFormula(data, context);
                context.vars.remove(newVar.label);
                return ExprLet.make(null, newVar, expr, sub);
            }
            case 14: {
                // ExprCall
                List<Func> preds = context.funcs.stream()
                        .filter(func -> func.isPred)
                        .collect(Collectors.toList());
                if (preds.isEmpty()) {
                    return ExprConstant.TRUE;
                }
                Func pred = pick(preds, data);

                // TODO: this might cause too many typechecking errors to not respect the decl expr
                // TODO: (maybe make them all univ?)
                List<Expr> args = new ArrayList<>();
                for (Decl decl : pred.decls) {
                    // *ignoring* the decl expr except for its arity
                    int arity = decl.expr.type().arity();
                    for (ExprHasName name : decl.names) {
                        args.add(makeExpr(data, arity, context));
                    }
                }
                return ExprCall.make(null, null, pred, args, 0L);
            }
            case 15: {
                // Noop
                return ExprUnary.Op.NOOP.make(null, makeFormula(data, context));
            }
        }
        throw new ErrorFatal("ASTFuzzTarget: unreachable!");
    }

    private static Expr makeExpr(FuzzedDataProvider data, int arity, FuzzContext context) {
        if (arity <= 0) {
            throw new ErrorFatal("ASTFuzzTarget: cannot make expression with arity <= 0");
        }
        switch (data.consumeInt(1, 16)) {
            case 1: {
                // ExprVar
                List<Expr> withArity = context.vars.keySet().stream()
                        .map(name -> context.vars.get(name))
                        .filter(entry -> entry.type == ContextEntry.Type.EXPR)
                        .filter(entry -> entry.arity == arity)
                        .map(entry -> entry.expr)
                        .collect(Collectors.toList());
                if (withArity.isEmpty()) {
                    return makeNoneWithArity(arity);
                }
                return pick(withArity, data);
            }
            case 2: {
                // ExprBinary with same arity on left and right
                ExprBinary.Op op = pick(Arrays.asList(
                        ExprBinary.Op.PLUS,
                        ExprBinary.Op.MINUS,
                        ExprBinary.Op.INTERSECT,
                        ExprBinary.Op.PLUSPLUS), data);
                return op.make(null, null, makeExpr(data, arity, context), makeExpr(data, arity, context));
            }
            case 3: {
                // Arrow
                // TODO: what to do about the multiplicities (need to be in for field decls)?
                if (arity == 1) {
                    return makeNoneWithArity(arity);
                }
                int leftArity = data.consumeInt(1, arity - 1);
                int rightArity = arity - leftArity;
                return makeExpr(data, leftArity, context).product(makeExpr(data, rightArity, context));
            }
            case 4: {
                // Join
                int leftArity = data.consumeInt(1, arity + 1);
                int rightArity = arity + 2 - leftArity;
                return makeExpr(data, leftArity, context).join(makeExpr(data, rightArity, context));
            }
            case 5: {
                // Domain, range
                Expr sub = makeExpr(data, arity, context);
                Expr restriction = makeExpr(data, 1, context);
                if (data.consumeBoolean()) {
                    return restriction.domain(sub);
                } else {
                    return sub.range(restriction);
                }
            }
            // TODO: SOMEOF, etc (for field decls)
            case 6: {
                // NOOP
                return ExprUnary.Op.NOOP.make(null, makeExpr(data, arity, context));
            }
            case 7: {
                // Transpose
                if (arity != 2) {
                    return makeNoneWithArity(arity);
                }
                return makeExpr(data, arity, context).transpose();
            }
            case 8: {
                // Closure
                if (arity != 2) {
                    return makeNoneWithArity(arity);
                }
                Expr sub = makeExpr(data, arity, context);
                if (data.consumeBoolean()) {
                    return sub.closure();
                } else {
                    return sub.reflexiveClosure();
                }
            }
            case 9: {
                // ExprConstant
                // *avoid* giving out univ to avoid quantifying over univ
                if (arity == 2 && data.consumeBoolean()) {
                    return ExprConstant.IDEN;
                }
                return makeNoneWithArity(arity);
            }
            case 10: {
                // ExprITE
                return makeFormula(data, context).ite(
                        makeExpr(data, arity, context), makeExpr(data, arity, context));
            }
            case 11: {
                // Comprehension
                List<String> addedVars = new ArrayList<>();

                int numVars = 0;
                List<Decl> decls = new ArrayList<>();
                while (numVars < arity) {
                    Expr expr = makeExpr(data, 1, context); // Portus only supports arity 1 here
                    int varsThisTime = data.consumeInt(1, Math.min(3, arity - numVars));
                    List<ExprVar> declVars = new ArrayList<>();
                    for (int j = 0; j < varsThisTime; j++) {
                        ExprVar newVar = ExprVar.make(null, makeName(data), expr.type());
                        declVars.add(newVar);
                        context.vars.put(newVar.label, new ContextEntry(newVar, 1, ContextEntry.Type.EXPR));
                        addedVars.add(newVar.label);
                    }
                    Decl decl = new Decl(null, null, null, null, declVars, expr);
                    decls.add(decl);
                    numVars += varsThisTime;
                }

                Expr sub = makeFormula(data, context);

                // remove the added vars to recover the context
                for (int i = addedVars.size() - 1; i >= 0; i--) {
                    context.vars.remove(addedVars.get(i));
                }

                return ExprQt.Op.COMPREHENSION.make(null, null, decls, sub);
            }
            case 12: {
                // Sig: *don't* return Int to avoid mixing Int and other sorts (like A+Int)
                if (arity != 1 || context.sigs.isEmpty()) {
                    return makeNoneWithArity(arity);
                }
                return pick(context.sigs, data);
            }
            case 13: {
                // ExprLet with formula
                Expr formula = makeFormula(data, context);
                ExprVar newVar = ExprVar.make(null, makeName(data), formula.type());
                context.vars.put(newVar.label, new ContextEntry(newVar, 1, ContextEntry.Type.FORMULA));
                Expr sub = makeExpr(data, arity, context);
                context.vars.remove(newVar.label);
                return ExprLet.make(null, newVar, formula, sub);
            }
            case 14: {
                int varArity = data.consumeInt(1, 3);
                Expr expr = makeExpr(data, varArity, context);
                ExprVar newVar = ExprVar.make(null, makeName(data), expr.type());
                Pair<Expr, Integer> varAndArity = new Pair<>(newVar, varArity);
                context.vars.put(newVar.label, new ContextEntry(newVar, varArity, ContextEntry.Type.EXPR));
                Expr sub = makeExpr(data, arity, context);
                context.vars.remove(newVar.label);
                return ExprLet.make(null, newVar, expr, sub);
            }
            case 15: {
                // ExprLet with integer expression
                Expr expr = makeIntExpr(data, context);
                ExprVar newVar = ExprVar.make(null, makeName(data), expr.type());
                context.vars.put(newVar.label, new ContextEntry(newVar, 1, ContextEntry.Type.INT));
                Expr sub = makeExpr(data, arity, context);
                context.vars.remove(newVar.label);
                return ExprLet.make(null, newVar, expr, sub);
            }
            case 16: {
                // ExprCall
                List<Func> funcs = context.funcs.stream()
                        .filter(func -> !func.isPred && func.returnDecl.type().arity() == arity)
                        .collect(Collectors.toList());
                if (funcs.isEmpty()) {
                    return makeNoneWithArity(arity);
                }
                Func func = pick(funcs, data);

                List<Expr> args = new ArrayList<>();
                for (Decl decl : func.decls) {
                    // *ignoring* the decl expr except for its arity
                    int declArity = decl.expr.type().arity();
                    for (ExprHasName name : decl.names) {
                        args.add(makeExpr(data, declArity, context));
                    }
                }
                return ExprCall.make(null, null, func, args, 0L);
            }
        }
        throw new ErrorFatal("ASTFuzzTarget: unreachable");
    }

    private static Expr makeNoneWithArity(int arity) {
        return tileWithArity(ExprConstant.EMPTYNESS, arity);
    }

    private static Expr tileWithArity(Expr expr, int arity) {
        if (arity <= 0) {
            throw new ErrorFatal("ASTFuzzTarget: cannot make expression with arity <= 0");
        }
        if (arity == 1) {
            return expr;
        }
        return tileWithArity(expr, arity - 1).product(expr);
    }

    private static Expr makeIntExpr(FuzzedDataProvider data, FuzzContext context) {
        switch (data.consumeInt(1, 10)) {
            case 1: {
                // ExprVar
                List<Expr> intVars = context.vars.keySet().stream()
                        .map(name -> context.vars.get(name))
                        .filter(entry -> entry.type == ContextEntry.Type.INT)
                        .map(entry -> entry.expr)
                        .collect(Collectors.toList());
                if (intVars.isEmpty()) {
                    return ExprConstant.makeNUMBER(0);
                }
                return pick(intVars, data);
            }
            case 2: {
                // ExprConstant
                if (data.consumeBoolean() || data.consumeBoolean()) {
                    return ExprConstant.makeNUMBER(data.consumeInt(-5000, 5000));
                } else {
                    return pick(Arrays.asList(ExprConstant.MAX, ExprConstant.MIN), data);
                }
            }
            case 3: {
                // ExprBinary
                // Exclude shift operators because Portus doesn't support them
                ExprBinary.Op op = pick(Arrays.asList(
                        ExprBinary.Op.IPLUS,
                        ExprBinary.Op.IMINUS,
                        ExprBinary.Op.MUL,
                        ExprBinary.Op.DIV,
                        ExprBinary.Op.REM), data);
                return op.make(null, null, makeIntExpr(data, context), makeIntExpr(data, context));
            }
            case 4: {
                // Various noops
                ExprUnary.Op op = pick(Arrays.asList(
                        ExprUnary.Op.NOOP,
                        ExprUnary.Op.CAST2INT,
                        ExprUnary.Op.CAST2SIGINT), data);
                return op.make(null, makeIntExpr(data, context));
            }
            case 5: {
                // Cardinality
                int arity = data.consumeInt(1, 3);
                return makeExpr(data, arity, context).cardinality();
            }
            case 6: {
                // ExprITE
                return makeFormula(data, context).ite(makeIntExpr(data, context), makeIntExpr(data, context));
            }
            case 7: {
                // ExprLet with formula
                Expr formula = makeFormula(data, context);
                ExprVar newVar = ExprVar.make(null, makeName(data), formula.type());
                context.vars.put(newVar.label, new ContextEntry(newVar, 1, ContextEntry.Type.FORMULA));
                Expr sub = makeIntExpr(data, context);
                context.vars.remove(newVar.label);
                return ExprLet.make(null, newVar, formula, sub);
            }
            case 8: {
                // ExprLet with expression
                int arity = data.consumeInt(1, 3);
                Expr expr = makeExpr(data, arity, context);
                ExprVar newVar = ExprVar.make(null, makeName(data), expr.type());
                Pair<Expr, Integer> varAndArity = new Pair<>(newVar, arity);
                context.vars.put(newVar.label, new ContextEntry(newVar, arity, ContextEntry.Type.EXPR));
                Expr sub = makeIntExpr(data, context);
                context.vars.remove(newVar.label);
                return ExprLet.make(null, newVar, expr, sub);
            }
            case 9: {
                // ExprLet with integer expression
                Expr expr = makeIntExpr(data, context);
                ExprVar newVar = ExprVar.make(null, makeName(data), expr.type());
                context.vars.put(newVar.label, new ContextEntry(newVar, 1, ContextEntry.Type.INT));
                Expr sub = makeIntExpr(data, context);
                context.vars.remove(newVar.label);
                return ExprLet.make(null, newVar, expr, sub);
            }
            case 10: {
                // ExprCall
                List<Func> funcs = context.funcs.stream()
                        .filter(func -> !func.isPred && func.returnDecl.equals(Sig.SIGINT))
                        .collect(Collectors.toList());
                if (funcs.isEmpty()) {
                    return ExprConstant.makeNUMBER(0);
                }
                Func func = pick(funcs, data);

                List<Expr> args = new ArrayList<>();
                for (Decl decl : func.decls) {
                    // *ignoring* the decl expr except for its arity
                    int declArity = decl.expr.type().arity();
                    for (ExprHasName name : decl.names) {
                        args.add(makeExpr(data, declArity, context));
                    }
                }
                return ExprCall.make(null, null, func, args, 0L);
            }
        }
        throw new ErrorFatal("ASTFuzzTarget: unreachable");
    }

    private static String makeName(FuzzedDataProvider data) {
        // 2-letter names, so it's easier to collide if we want to + no keywords (but don't allow "in")
        String validFirstChars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_\"";
        // Sketchy solution: remove "n" from the next chars so we can't make "in"
        String validNextChars = "abcdefghijklmopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_\"1234567890";
        char first = validFirstChars.charAt(data.consumeInt(0, validFirstChars.length() - 1));
        char next = validNextChars.charAt(data.consumeInt(0, validNextChars.length() - 1));
        return new String(new char[] {first, next});
    }

}
