/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2023 The jConstraints Authors
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

import com.microsoft.z3.ApplyResult;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Global;
import com.microsoft.z3.Goal;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Tactic;
import com.microsoft.z3.Z3Exception;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.QuantifierEliminator;
import gov.nasa.jpf.constraints.api.Simplifier;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.logging.Logger;

public class NativeZ3Solver extends ConstraintSolver
    implements QuantifierEliminator, Simplifier<Boolean>, UNSATCoreSolver {

  private static final Logger logger = Logger.getLogger("constraints");

  private Context ctx;

  private NativeZ3SolverContext defaultContext;

  private final int timeout;

  private final Map<String, String> options;

  private boolean unsatTracking = false;

  static {
    // This has to be set globally
    // TODO: this should be moved to options as well
    Global.setParameter("smt.bv.enable_int2bv", "true");
    Global.setParameter("pp.decimal", "true");
    Global.setParameter("model", "true");
  }

  public NativeZ3Solver() {
    this(-1, new HashMap<String, String>());
  }

  public NativeZ3Solver(final int to, final Map<String, String> properties) {
    super.name = "Z3";

    this.timeout = to;
    this.options = properties;

    init();
  }

  Context getContext() {
    return ctx;
  }

  private void init() {
    for (final Entry<String, String> o : options.entrySet()) {
      Global.setParameter(o.getKey(), o.getValue());
    }

    try {
      this.ctx = new Context();
      defaultContext = createContext();
    } catch (final Z3Exception ex) {
      if (ctx != null) {
        // FIXME
        try {
          // ctx.dispose();
        } catch (final Throwable t) {
        }
      }
      throw new RuntimeException(ex);
    }
  }

  public void dispose() {
    defaultContext.dispose();
    defaultContext = null;
    ctx.close();
    ctx = null;
  }

  @Override
  protected void finalize() throws Throwable {
    super.finalize();
    if (ctx != null) {
      dispose();
    }
  }

  @Override
  public Result solve(final Expression<Boolean> f, final Valuation result) {
    try {
      defaultContext.push();
      defaultContext.add(f);
      return defaultContext.solve(result);
    } finally {
      defaultContext.pop();
    }
  }

  @Override
  public NativeZ3SolverContext createContext() {
    Solver solver = null;

    try {
      solver = ctx.mkSolver();
      final NativeZ3ExpressionGenerator root;

      if (timeout > 0) {
        final Params p = ctx.mkParams();
        // p.add("timeout",timeout);
        // p.add(":timeout", timeout);
        p.add("timeout", timeout);
        solver.setParameters(p);
      }

      root = new NativeZ3ExpressionGenerator(ctx, solver);
      NativeZ3SolverContext res = new NativeZ3SolverContext(solver, root);
      if (unsatTracking) {
        res.enableUnsatTracking();
      }

      return res;
    } catch (final Z3Exception ex) {
      if (solver != null) {
        try {
          // solver.dispose();
        } catch (final Throwable t) {
        }
      }
      throw new RuntimeException(ex);
    }
  }

  @Override
  public Expression eliminateQuantifiers(final Expression<Boolean> expr) {
    final Solver solver = ctx.mkSolver();
    final NativeZ3ExpressionGenerator rootGenerator = new NativeZ3ExpressionGenerator(ctx, solver);
    final Tactic tactic = ctx.mkTactic("qe");
    // The booleans are model genertation, unsat core, proof generation
    final Goal goal = ctx.mkGoal(true, false, false);

    final BoolExpr z3Expr = rootGenerator.generateAssertion(expr);
    goal.add(z3Expr);

    final ApplyResult res = tactic.apply(goal);
    final Goal[] subgoals = res.getSubgoals();
    try {
      return convertSubgoals(subgoals);
    } catch (ImpreciseRepresentationException e) {
      throw new RuntimeException(e);
    }
  }

  @Override
  public Expression<Boolean> simplify(final Expression<Boolean> expr) {
    final Solver solver = ctx.mkSolver();
    final NativeZ3ExpressionGenerator rootGenerator = new NativeZ3ExpressionGenerator(ctx, solver);

    final Tactic tactic = ctx.mkTactic("ctx-solver-simplify");
    final Goal goal = ctx.mkGoal(true, false, false);

    final BoolExpr z3Expr = rootGenerator.generateAssertion(expr);
    goal.add(z3Expr);

    final ApplyResult res = tactic.apply(goal);
    if (res.getNumSubgoals() == 1
        && (res.getSubgoals()[0].isDecidedSat() || res.getSubgoals()[0].isDecidedUnsat())) {

      logger.warning("Simplification failed.");
      return expr;
    }

    final Goal[] subgoals = res.getSubgoals();
    try {
      return convertSubgoals(subgoals);
    } catch (ImpreciseRepresentationException e) {
      throw new RuntimeException(e);
    }
  }

  private Expression<Boolean> convertSubgoals(final Goal[] subgoals)
      throws ImpreciseRepresentationException {
    Expression result = null;
    final NativeZ3TojConstraintConverter converter = new NativeZ3TojConstraintConverter();
    for (final Goal g : subgoals) {
      final BoolExpr[] formulas = g.getFormulas();
      for (final BoolExpr f : formulas) {
        final Expression<Boolean> jConstraintExpr = (Expression<Boolean>) converter.parse(f);
        result = (result == null) ? jConstraintExpr : ExpressionUtil.and(result, jConstraintExpr);
      }
    }
    return result;
  }

  @Override
  public void enableUnsatTracking() {
    dispose();
    Global.setParameter("unsat_core", "true");
    init();
    unsatTracking = true;
  }

  @Override
  public void disableUnsatTracking() {
    dispose();
    Global.setParameter("unsat_core", "false");
    init();
    unsatTracking = false;
  }

  @Override
  public List<Expression<Boolean>> getUnsatCore() {
    return defaultContext.getUnsatCore();
  }
}
