/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2026 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package gov.nasa.jpf.constraints.solvers.nativez3;

import com.microsoft.z3.AST;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FPNum;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import gov.nasa.jpf.constraints.util.TypeUtil;
import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class NativeZ3SolverContext extends SolverContext implements UNSATCoreSolver {

  private static final Logger logger = Logger.getLogger("constraints");

  private final Deque<NativeZ3ExpressionGenerator> generatorStack = new ArrayDeque<>();
  private final Deque<Expression<Boolean>> expressionStack = new ArrayDeque<>();
  private final Deque<Map<String, Variable<?>>> freeVarsStack = new ArrayDeque<>();

  private Solver solver;

  /** the asserted expressions per scope (for {@link #solveIndependent}) */
  private final Deque<List<Expression<Boolean>>> assertionStack = new ArrayDeque<>();

  /**
   * solve independent groups of the assertions (no shared variables or functions) separately, each
   * with a fresh, non-incremental solver, see {@link IndependentConstraints}
   */
  private boolean independence = true;

  /** solver timeout in milliseconds (budget of a call of {@link #solve}), -1 for none */
  private int timeout = -1;

  void setIndependence(boolean independence) {
    this.independence = independence;
  }

  void setTimeout(int timeout) {
    this.timeout = timeout;
  }

  private final Pattern bytePattern =
      Pattern.compile("(?:[^\\\\]|^)(?<toBeReplaced>\\\\x(?<digits>[0-9a-f]{2}))");

  private boolean unsatTracking = false;
  private int tracker = 0;
  private final Map<Expr<BoolSort>, Expression<Boolean>> tracking = new HashMap<>();

  /**
   * strings are Java strings (see NativeZ3ExpressionGenerator), for the generators of this context
   */
  void setJavaStrings(boolean javaStrings) {
    for (NativeZ3ExpressionGenerator g : generatorStack) {
      g.setJavaStrings(javaStrings);
    }
  }

  public NativeZ3SolverContext(
      final Solver solver, final NativeZ3ExpressionGenerator rootGenerator) {
    this.solver = solver;
    this.generatorStack.push(rootGenerator);
    this.expressionStack.push(ExpressionUtil.TRUE);
    this.freeVarsStack.push(new HashMap<String, Variable<?>>());
    this.assertionStack.push(new ArrayList<>());
  }

  @Override
  public void push() {
    try {
      solver.push();
      final Map<String, Variable<?>> fvMap = freeVarsStack.peek();
      generatorStack.push(generatorStack.peek().createChild());
      freeVarsStack.push(new HashMap<String, Variable<?>>(fvMap));
      expressionStack.push(ExpressionUtil.TRUE);
      assertionStack.push(new ArrayList<>());
    } catch (final Z3Exception ex) {
      throw new RuntimeException(ex);
    }
  }

  @Override
  public void pop(final int n) {
    for (int i = 0; i < n; i++) {
      final NativeZ3ExpressionGenerator gen = generatorStack.pop();
      gen.dispose();
      freeVarsStack.pop();
      expressionStack.pop();
      assertionStack.pop();
    }
    try {
      solver.pop(n);
    } catch (final Z3Exception ex) {
      throw new RuntimeException(ex);
    }
  }

  public Result approximate(final Valuation val) {
    logger.finer("Solving ...");
    try {
      final Status status = solver.check();
      if (status != Status.SATISFIABLE || val == null) {
        logger.finer("Not satisfiable: " + status);

        if (status == Status.UNSATISFIABLE) {
          logger.finest("unsat core: ");
          for (final Expr e : solver.getUnsatCore()) {
            logger.finest("  " + e.getSExpr());
          }
        }

        return translateStatus(status);
      }

      Model model = solver.getModel();
      try {
        if (logger.isLoggable(Level.FINE)) {
          final String modelText = model.toString().replace("\n", ", ").trim();
          logger.fine(modelText);
        }

        final NativeZ3ExpressionGenerator gen = generatorStack.peek();
        if (gen.isTainted(model)) {
          //          model.dispose();
          logger.info("Model is tainted, rechecking ...");
          model = gen.recheckUntainted();
          if (model == null) {
            return Result.DONT_KNOW;
          }
        }

        // FIXME mi: using origVars here fixes the issue that variables occuring only in the
        //           scope of quantifiers are part of the valuation. Might it break something
        //           else?
        final long max = model.getNumConsts();
        final FuncDecl[] decls = model.getConstDecls();
        try {
          try {
            val.putAll(parseModel(model, true));
          } catch (ImpreciseRepresentationException e) {
            throw new RuntimeException("Imprecise Representation");
          }

        } finally {
          for (int i = 0; i < decls.length; i++) {
            //            decls[i].dispose();
          }
        }

      } finally {
        //        model.dispose();
      }

      logger.finer("Satisfiable, valuation " + val);
      return Result.SAT;
    } catch (final Z3Exception ex) {
      if (isSolverGivingUp(ex)) {
        logger.info("Z3 gave up: " + ex.getMessage());
        return Result.DONT_KNOW;
      }
      throw new RuntimeException(ex);
    }
  }

  @Override
  public Result solve(final Valuation val) {
    logger.finer("Solving ...");
    if (independence && !unsatTracking) {
      return solveIndependent(val);
    }
    try {
      final Status status = solver.check();
      if (status != Status.SATISFIABLE || val == null) {
        logger.finer("Not satisfiable: " + status);

        if (status == Status.UNSATISFIABLE) {
          logger.finest("unsat core: ");
          for (final Expr e : solver.getUnsatCore()) {
            logger.finest("  " + e.getSExpr());
          }
        }

        return translateStatus(status);
      }

      Model model = solver.getModel();
      try {
        if (logger.isLoggable(Level.FINE)) {
          final String modelText = model.toString().replace("\n", ", ").trim();
          logger.fine(modelText);
        }

        final NativeZ3ExpressionGenerator gen = generatorStack.peek();
        if (gen.isTainted(model)) {
          //          model.dispose();
          logger.info("Model is tainted, rechecking ...");
          model = gen.recheckUntainted();
          if (model == null) {
            return Result.DONT_KNOW;
          }
        }

        // FIXME mi: using origVars here fixes the issue that variables occuring only in the
        //           scope of quantifiers are part of the valuation. Might it break something
        //           else?
        final long max = model.getNumConsts();
        final FuncDecl[] decls = model.getConstDecls();
        try {
          try {
            val.putAll(parseModel(model));
          } catch (ImpreciseRepresentationException e) {
            Valuation testVal = new Valuation();
            testVal.putAll(val);
            try {
              testVal.putAll(parseModel(model, true));
              if (validateExpressionStack(testVal)) {
                val.putAll(testVal, true);
              } else {
                throw new ImpreciseRepresentationException(
                    "Cannot fix the imprecise " + "Representation");
              }
            } catch (ImpreciseRepresentationException e2) {
              throw new RuntimeException("Imprecise Representation");
            }
          }

        } finally {
          for (int i = 0; i < decls.length; i++) {
            //            decls[i].dispose();
          }
        }

      } finally {
        //        model.dispose();
      }

      logger.finer("Satisfiable, valuation " + val);
      return Result.SAT;
    } catch (final Z3Exception ex) {
      if (isSolverGivingUp(ex)) {
        logger.info("Z3 gave up: " + ex.getMessage());
        return Result.DONT_KNOW;
      }
      throw new RuntimeException(ex);
    }
  }

  /**
   * Solves the independent groups of the assertions (see {@link IndependentConstraints}) one after
   * the other, each with a fresh solver and expression generator (side constraints of the
   * translation, e.g. string length bounds, go to the solver of the group). UNSAT if a group is
   * UNSAT, SAT with the union of the models if all are SAT, DONT_KNOW otherwise. The timeout is the
   * budget of the whole call.
   */
  private Result solveIndependent(final Valuation val) {
    final List<Expression<Boolean>> conjuncts = new ArrayList<>();
    for (final List<Expression<Boolean>> scope : assertionStack) {
      for (final Expression<Boolean> e : scope) {
        IndependentConstraints.flatten(e, conjuncts);
      }
    }
    final List<List<Expression<Boolean>>> groups = IndependentConstraints.partition(conjuncts);
    logger.finer(groups.size() + " independent groups of " + conjuncts.size() + " conjuncts");

    final NativeZ3ExpressionGenerator current = generatorStack.peek();
    final long deadline = timeout > 0 ? System.currentTimeMillis() + timeout : Long.MAX_VALUE;
    final Valuation result = new Valuation();
    boolean unknown = false;
    for (final List<Expression<Boolean>> group : groups) {
      final long remaining = deadline - System.currentTimeMillis();
      if (remaining <= 0) {
        return Result.DONT_KNOW;
      }
      try {
        final Solver s = current.ctx.mkSolver();
        if (timeout > 0) {
          final Params p = current.ctx.mkParams();
          p.add("timeout", (int) Math.min(remaining, Integer.MAX_VALUE));
          s.setParameters(p);
        }
        if (IndependentConstraints.usesStrings(group)) {
          // after a push, Z3 uses its incremental SMT core; for strings (mixed with bitvectors,
          // e.g. the hash
          // codes of strings), it is much faster than the strategy chosen for the logic of a
          // non-incremental
          // query, which in turn is much faster for floating-point and bitvector constraints
          // (bit-blasting)
          s.push();
        }
        final NativeZ3ExpressionGenerator gen = new NativeZ3ExpressionGenerator(current.ctx, s);
        gen.setJavaStrings(current.isJavaStrings());
        final BoolExpr[] exprs = new BoolExpr[group.size()];
        final Map<String, Variable<?>> vars = new HashMap<>();
        for (int i = 0; i < exprs.length; i++) {
          exprs[i] = gen.generateAssertion(group.get(i));
          for (final Variable<?> v : ExpressionUtil.freeVariables(group.get(i))) {
            vars.put(v.getName(), v);
          }
        }
        s.add(exprs);
        final Status status = s.check();
        if (status == Status.UNSATISFIABLE) {
          return Result.UNSAT;
        }
        if (status != Status.SATISFIABLE) {
          unknown = true;
          continue;
        }
        if (val == null || unknown) {
          continue;
        }
        Model model = s.getModel();
        if (gen.isTainted(model)) {
          logger.info("Model is tainted, rechecking ...");
          model = gen.recheckUntainted();
          if (model == null) {
            unknown = true;
            continue;
          }
        }
        try {
          result.putAll(parseModel(model, false, vars));
        } catch (ImpreciseRepresentationException e) {
          final Valuation testVal = new Valuation();
          testVal.putAll(result);
          try {
            testVal.putAll(parseModel(model, true, vars));
          } catch (ImpreciseRepresentationException e2) {
            throw new RuntimeException("Imprecise Representation");
          }
          if (!ExpressionUtil.and(group).evaluate(testVal)) {
            throw new ImpreciseRepresentationException("Cannot fix the imprecise Representation");
          }
          result.putAll(testVal, true);
        }
      } catch (final Z3Exception ex) {
        if (isSolverGivingUp(ex)) {
          logger.info("Z3 gave up: " + ex.getMessage());
          unknown = true;
          continue;
        }
        throw new RuntimeException(ex);
      } catch (final ImpreciseRepresentationException ex) {
        throw new RuntimeException(ex);
      }
    }
    if (unknown) {
      return Result.DONT_KNOW;
    }
    if (val != null) {
      // variables known to the context, but in no assertion (e.g. from an expression that could not
      // be added)
      for (final Variable<?> v : freeVarsStack.peek().values()) {
        if (!result.containsValueFor(v)) {
          result.setDefaultValue(v);
        }
      }
      val.putAll(result);
      logger.finer("Satisfiable, valuation " + val);
    }
    return Result.SAT;
  }

  private boolean validateExpressionStack(Valuation val) {
    Expression<Boolean> combined = ExpressionUtil.and(expressionStack);
    return combined.evaluate(val);
  }

  private Valuation parseModel(final Model model) throws ImpreciseRepresentationException {
    return parseModel(model, false);
  }

  private Valuation parseModel(final Model model, boolean unsafe)
      throws ImpreciseRepresentationException {
    return parseModel(model, unsafe, freeVarsStack.peek());
  }

  /** the values of {@code variables} in {@code model} (default values for those without one) */
  private Valuation parseModel(
      final Model model, boolean unsafe, Map<String, Variable<?>> variables)
      throws ImpreciseRepresentationException {
    Valuation val = new Valuation();

    final Map<String, Variable<?>> freeVars = new HashMap<>(variables);
    final long max = model.getNumConsts();
    final FuncDecl[] decls = model.getConstDecls();
    for (int i = 0; i < max; i++) {
      final FuncDecl decl = decls[i];
      Symbol sym = null;
      String text = null;
      try {
        sym = decl.getName();
        text = sym.toString().trim();
      } finally {
        //              sym.dispose();
      }

      final Variable<?> v = freeVars.get(text);
      if (v == null || v.getType() instanceof gov.nasa.jpf.constraints.types.ArrayType) {
        // arrays have no Java values
        continue;
      }
      freeVars.remove(text);

      final AST res = model.getConstInterp(decl);
      final String value = res.toString().trim();
      if (res instanceof FPNum) {
        FPNum resFP = (FPNum) res;
        int width = resFP.getEBits() + resFP.getSBits();
        switch (width) {
          case 32:
            float f;
            if (resFP.isInf()) {
              f = resFP.getSign() ? Float.NEGATIVE_INFINITY : Float.POSITIVE_INFINITY;
            } else if (resFP.isZero()) {
              f = resFP.getSign() ? -0.0f : +0.0f;
            } else if (resFP.isNaN()) {
              f = Float.NaN;
            } else {
              String mString = resFP.getSignificandBV().toString();
              String eString = resFP.getExponentBV(true).toString();
              int mbits =
                  mString.startsWith("#x")
                      ? Integer.decode(mString.replace("#", "0"))
                      : Integer.parseInt(mString.replace("#b", ""), 2);
              int eBits =
                  eString.startsWith("#x")
                      ? Integer.decode(eString.replace("#", "0"))
                      : Integer.parseInt(eString.replace("#b", ""), 2);

              int allbits = mbits | (eBits << 23);
              if (resFP.getSign()) {
                allbits |= (1 << 31);
              }

              f = Float.intBitsToFloat(allbits);
            }
            val.setValue((Variable<Float>) v, f);
            break;
          case 64:
            double d;
            if (resFP.isInf()) {
              d = resFP.getSign() ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
            } else if (resFP.isZero()) {
              d = resFP.getSign() ? -0.0 : +0.0;
            } else if (resFP.isNaN()) {
              d = Double.NaN;
            } else {
              String mString = resFP.getSignificandBV().toString();
              String eString = resFP.getExponentBV(true).toString();
              long mbits =
                  mString.startsWith("#x")
                      ? Long.decode(mString.replace("#", "0"))
                      : Long.parseLong(mString.replace("#b", ""), 2);
              int eBits =
                  eString.startsWith("#x")
                      ? Integer.decode(eString.replace("#", "0"))
                      : Integer.parseInt(eString.replace("#b", ""), 2);

              long allbits = mbits | (((long) eBits) << 52);
              if (resFP.getSign()) {
                allbits |= (1L << 63);
              }

              d = Double.longBitsToDouble(allbits);
            }
            val.setValue((Variable<Double>) v, d);
            break;
          default:
            throw new IllegalArgumentException("Cannot parse the FP value");
        }
        continue;
      } else if (TypeUtil.isRealSort(v) && value.contains("/")) {
        final String[] split = value.split("/");
        final BigDecimal nom = new BigDecimal(split[0].trim());
        final BigDecimal den = new BigDecimal(split[1].trim());
        final BigDecimal quot = nom.divide(den, 10, RoundingMode.FLOOR);
        if (unsafe) {
          val.setUnsafeParsedValue(v, quot.toPlainString());
        } else {
          val.setParsedValue(v, quot.toPlainString());
        }
      } else if (TypeUtil.isRealSort(v)) {
        // Z3 might print a question mark at the end of the number, if it is an inexact
        // representation
        // and Z3 is aware of the inexact representation. Java cannot handle the question
        // mark.
        // TODO: How to do this right.
        // Z3 return originally: (root-obj (+ (^ x 2) (- 2)) 2) for root of 2.
        String tmpValue = value.replace("?", "");
        if (unsafe) {
          val.setUnsafeParsedValue(v, tmpValue);
        } else {
          val.setParsedValue(v, tmpValue);
        }
      } else if (v.getType().equals(BuiltinTypes.STRING)) {
        String sValue = value;
        if (sValue.startsWith("\"") && sValue.endsWith("\"")) {
          sValue = sValue.substring(1, value.length() - 1);
        }
        val.setValue((Variable<String>) v, unescapeStringLiteral(sValue));
      } else {
        if (unsafe) {
          val.setUnsafeParsedValue(v, value);

        } else {
          val.setParsedValue(v, value);
        }
      }
    }
    for (final Variable<?> r : freeVars.values()) {
      val.setDefaultValue(r);
    }
    return val;
  }

  @Override
  public void dispose() {
    while (!generatorStack.isEmpty()) {
      generatorStack.pop().dispose();
    }
    freeVarsStack.clear();

    try {
      //      solver.dispose();
    } catch (final Z3Exception ex) {
    } finally {
      solver = null;
    }
  }

  @Override
  protected void finalize() throws Throwable {
    super.finalize();

    if (solver != null) {
      dispose();
    }
  }

  @Override
  public void add(final List<Expression<Boolean>> expressions) {
    final BoolExpr[] exprs = new BoolExpr[expressions.size()];

    final NativeZ3ExpressionGenerator gen = generatorStack.peek();

    final Map<String, Variable<?>> fvMap = freeVarsStack.peek();

    int i = 0;
    try {
      for (final Expression<Boolean> ex : expressions) {
        // logger.finer("Checking " + ex);
        exprs[i++] = gen.generateAssertion(ex);
        final Set<Variable<?>> fvs = ExpressionUtil.freeVariables(ex);
        for (final Variable<?> v : fvs) {
          fvMap.put(v.getName(), v);
        }
      }

      if (unsatTracking) {
        addAndTrack(exprs, expressions);
      } else {
        normalAdd(exprs);
      }
      // recorded only once added: an expression that cannot be translated is not part of the
      // problem
      Expression<Boolean> currentExpression = expressionStack.pop();
      expressionStack.push(ExpressionUtil.and(currentExpression, ExpressionUtil.and(expressions)));
      assertionStack.peek().addAll(expressions);
    } catch (final Z3Exception ex) {
      throw new RuntimeException(ex);
    } finally {
      // !!! This is a very important corner case. Sometimes, the expression
      // might just be a single boolean variable, WHICH MAY BE PROTECTED!
      gen.safeDispose(exprs);
    }
  }

  private void normalAdd(final Expr<BoolSort>[] exprs) {
    solver.add(exprs);
  }

  private void addAndTrack(final Expr<BoolSort>[] exprs, final List<Expression<Boolean>> jExprs) {
    BoolExpr[] trackerVars = new BoolExpr[exprs.length];
    for (int idx = 0; idx < exprs.length; ++idx) {
      Variable trackVar = Variable.create(BuiltinTypes.BOOL, "track" + ++tracker);
      BoolExpr z3Var = (BoolExpr) generatorStack.peek().createBoolVar(trackVar);
      trackerVars[idx] = z3Var;
      tracking.put(z3Var, jExprs.get(idx));
    }
    solver.assertAndTrack(exprs, trackerVars);
  }

  private static Result translateStatus(final Status status) {
    switch (status) {
      case SATISFIABLE:
        return Result.SAT;
      case UNSATISFIABLE:
        return Result.UNSAT;
      default: // case UNKNOWN:
        return Result.DONT_KNOW;
    }
  }

  @Override
  public String toString() {
    final StringBuilder sb = new StringBuilder();
    try {
      for (final BoolExpr e : this.solver.getAssertions()) {
        sb.append(e.getSExpr()).append("\n");
      }
    } catch (final Z3Exception ex) {
      sb.append("Error: ").append(ex.getMessage());
    }
    return sb.toString();
  }

  @Override
  public void enableUnsatTracking() {
    unsatTracking = true;
  }

  @Override
  public void disableUnsatTracking() {
    unsatTracking = false;
  }

  @Override
  public List<Expression<Boolean>> getUnsatCore() {
    List<Expr> unsatCore = Arrays.asList(solver.getUnsatCore());
    List<Expression<Boolean>> jUnsatCore = new LinkedList<>();
    for (Expr e : unsatCore) {
      jUnsatCore.add(tracking.get(e));
    }
    return jUnsatCore;
  }

  /**
   * The content of a string literal of a Z3 model: {@code ""} is a double quote, {@code \\u{h..h}},
   * {@code \\uhhhh}, and {@code \\xhh} are characters given by their code (Z3 writes non-printable
   * and non-ASCII characters this way), any other backslash is itself.
   */
  static String unescapeStringLiteral(String literal) {
    StringBuilder sb = new StringBuilder();
    int i = 0;
    while (i < literal.length()) {
      char c = literal.charAt(i);
      if (c == '"' && literal.startsWith("\"", i + 1)) {
        sb.append('"');
        i += 2;
        continue;
      }
      if (c == '\\') {
        Matcher m = ESCAPE.matcher(literal).region(i, literal.length());
        if (m.lookingAt()) {
          String hex =
              m.group(1) != null ? m.group(1) : m.group(2) != null ? m.group(2) : m.group(3);
          sb.appendCodePoint(Integer.parseInt(hex, 16));
          i = m.end();
          continue;
        }
      }
      sb.append(c);
      i++;
    }
    return sb.toString();
  }

  /** escape sequences of characters in Z3 string literals: \\u{h..h}, \\uhhhh, \\xhh */
  private static final Pattern ESCAPE =
      Pattern.compile("\\\\u\\{([0-9a-fA-F]{1,6})\\}|\\\\u([0-9a-fA-F]{4})|\\\\x([0-9a-fA-F]{2})");

  /**
   * Z3 exceptions that mean that the query is undecided (e.g. the string solver reached its limit
   * of unfolding recursive definitions), not that it is malformed: the result is DONT_KNOW.
   */
  static boolean isSolverGivingUp(Z3Exception ex) {
    String m = String.valueOf(ex.getMessage()).toLowerCase();
    return m.contains("max unfolding")
        || m.contains("canceled")
        || m.contains("timeout")
        || m.contains("resource limit");
  }
}
