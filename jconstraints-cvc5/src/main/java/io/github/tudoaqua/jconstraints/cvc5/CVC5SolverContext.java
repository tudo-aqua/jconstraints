/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2022 The jConstraints Authors
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

  public CVC5SolverContext() {
    ctx = new Solver();
    ctx.setOption("produce-models", "true");
    ctx.setOption("output-language", "smt");
    ctx.setOption("strings-exp", "true");
    ctx.setOption("seed", "1234");
    ctx.setOption("sat-random-seed", "1234");
    varsHistory = new LinkedList<>();
    varsHistory.push(new HashMap());
  }

  @Override
  public void push() {
    try {
      ctx.push();
    } catch (CVC5ApiException e) {
      throw new RuntimeException(e);
    }
    varsHistory.push(new HashMap(vars));
  }

  @Override
  public void pop() {
    try {
      ctx.pop();
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
    Result res = ctx.checkSat();
    if (res.toString().toLowerCase().equals("sat")) {
      try {
        CVC5Solver.getModel(valuation, vars, ctx);
      } catch (CVC5ApiException e) {
        throw new RuntimeException(e);
      }
    }
    return CVC5Solver.convertCVC4Res(res);
  }

  @Override
  public void add(List<Expression<Boolean>> list) {
    CVC5ExpressionGenerator gen = new CVC5ExpressionGenerator(ctx, vars);
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
  public List<Expression<Boolean>> getUnsatCore() {
    Term[] core = ctx.getUnsatCore();
    List<Expression<Boolean>> jCore = new LinkedList<>();
    for (Term e : core) {
      jCore.add(expressions.get(e.getId()));
    }
    return jCore;
  }
}
