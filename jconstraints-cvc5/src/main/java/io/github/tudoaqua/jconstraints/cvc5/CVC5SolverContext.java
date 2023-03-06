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

package io.github.tudoaqua.jconstraints.cvc5;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.solvers.datastructures.ExpressionStack;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Result;
import io.github.cvc5.Solver;
import io.github.cvc5.Term;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class CVC5SolverContext extends SolverContext implements UNSATCoreSolver {

  private Solver ctx;

  private HashMap<Variable, Term> vars = new HashMap<>();
  private LinkedList<HashMap<Variable, Term>> varsHistory;

  private boolean isCoreTracking = false;
  private Map<Long, Expression<Boolean>> expressions = new HashMap<Long, Expression<Boolean>>();
  private ExpressionStack es = new ExpressionStack();

  public CVC5SolverContext() {
    ctx = initSolver();
    varsHistory = new LinkedList<>();
    varsHistory.push(new HashMap());
  }

  private Solver initSolver() {
    Solver c = new Solver();
    c.setOption("produce-models", "true");
    c.setOption("output-language", "smt");
    c.setOption("strings-exp", "true");
    c.setOption("seed", "1234");
    c.setOption("sat-random-seed", "1234");
    return c;
  }

  @Override
  public void push() {
    try {
      ctx.push();
      es.push();
    } catch (CVC5ApiException e) {
      throw new RuntimeException(e);
    }
    varsHistory.push(new HashMap(vars));
  }

  @Override
  public void pop() {
    try {
      ctx.pop();
      es.pop(1);
    } catch (CVC5ApiException e) {
      throw new RuntimeException(e);
    }
    vars = varsHistory.pop();
  }

  @Override
  public void pop(int i) {
    for (int j = 0; j < i; j++) {
      this.pop();
    }
  }

  /** The valuation is only filled with data, if the expressions in the context are satisfiable. */
  @Override
  public ConstraintSolver.Result solve(Valuation valuation) {
    try {
      Result res = ctx.checkSat();
      if (res.toString().toLowerCase().equals("sat")) {
        CVC5Solver.getModel(valuation, vars, ctx);
      }
      return CVC5Solver.convertCVC4Res(res);
    } catch (CVC5ApiException e) {
      try {
        return secondTry(valuation);
      } catch (CVC5ApiException e2) {
        throw new RuntimeException(e2);
      }
    }
  }

  private ConstraintSolver.Result secondTry(Valuation val) throws CVC5ApiException {
    // FIXME, this seems push pop realted in the CVC5 api. Otherwise, this should make no difference
    // to using the context.
    Solver ctx2 = initSolver();
    HashMap<Variable, Term> vars2 = new HashMap<>();
    Term expr =
        new CVC5ExpressionGenerator(ctx2, vars2)
            .generateExpression(ExpressionUtil.and(es.getCurrentExpression()));
    ConstraintSolver.Result jRes = CVC5Solver.convertCVC4Res(ctx2.checkSatAssuming(expr));
    if (jRes.equals(ConstraintSolver.Result.SAT)) {
      CVC5Solver.getModel(val, vars2, ctx2);
    }
    return jRes;
  }

  @Override
  public void add(List<Expression<Boolean>> list) {
    CVC5ExpressionGenerator gen = new CVC5ExpressionGenerator(ctx, vars);
    es.add(list);
    for (Expression<Boolean> l : list) {
      Term expr = gen.generateExpression(l);
      if (isCoreTracking) {
        expressions.put(expr.getId(), l);
      }
      ctx.assertFormula(expr);
    }
    vars = gen.getVars();
  }

  @Override
  public void dispose() {
    ctx.close();
  }

  @Override
  public void enableUnsatTracking() {
    ctx.setOption("produce-unsat-cores", "true");
    isCoreTracking = true;
  }

  @Override
  public void disableUnsatTracking() {
    ctx.setOption("produce-unsat-cores", "false");
    isCoreTracking = false;
  }

  @Override
  public List<Expression<Boolean>> getUnsatCore() {
    if (!isCoreTracking) return null;
    Term[] core = ctx.getUnsatCore();
    List<Expression<Boolean>> jCore = new LinkedList<>();
    for (Term e : core) {
      jCore.add(expressions.get(e.getId()));
    }
    return jCore;
  }
}
