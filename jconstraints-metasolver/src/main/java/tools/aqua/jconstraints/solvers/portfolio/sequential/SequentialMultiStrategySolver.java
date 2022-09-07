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

package tools.aqua.jconstraints.solvers.portfolio.sequential;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import io.github.tudoaqua.jconstraints.cvc5.CVC5Solver;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;

public class SequentialMultiStrategySolver extends ConstraintSolver {
  static final String CVC5 = "cvc5";
  static final String Z3 = "z3";
  Properties usedProperties;

  private final Map<String, ConstraintSolver> solvers;
  private boolean isCVC5enabled = true;
  private boolean isCoreCheckingEnabled = true;

  public SequentialMultiStrategySolver(Properties properties) {
    solvers = new HashMap<>();
    setupSolvers(properties);
  }

  @Override
  public Result solve(Expression<Boolean> expression, Valuation valuation) {
    StringOrFloatExpressionVisitor visitor = new StringOrFloatExpressionVisitor();
    boolean isStringOrFloatExpression = expression.accept(visitor, null);
    if (isCVC5enabled && isStringOrFloatExpression) {
      Result res = solvers.get(CVC5).solve(expression, valuation);
      if (res.equals(Result.SAT)) {
        try {
          boolean evaluation = expression.evaluateSMT(valuation);
          if (!evaluation) {
            res = Result.DONT_KNOW;
          }
        } catch (Exception e) {
          res = Result.DONT_KNOW;
        }
      }
      if (res.equals(Result.UNSAT)) {
        return res;
      } else {
        isCVC5enabled = false;
        System.out.println("Disable process solver and shutdown exec");
        return solve(expression, valuation);
      }
    } else {
      return solvers.get(Z3).solve(expression, valuation);
    }
  }

  @Override
  public SolverContext createContext() {
    Map<String, SolverContext> ctxs = new HashMap<>();
    for (Entry<String, ConstraintSolver> s : solvers.entrySet()) {
      ConstraintSolver solver = s.getValue();
      ctxs.put(s.getKey(), solver.createContext());
    }
    return new SequentialMultiStrategySolverContext(ctxs, isCoreCheckingEnabled);
  }

  private void setupSolvers(Properties properties) {
    usedProperties = properties;
    ConstraintSolver cvc5 = ConstraintSolverFactory.createSolver(CVC5, properties);
    ConstraintSolver z3 = ConstraintSolverFactory.createSolver(Z3, properties);
    if (isCoreCheckingEnabled) {
      ((UNSATCoreSolver) cvc5).enableUnsatTracking();
      ((UNSATCoreSolver) z3).enableUnsatTracking();
    }
    solvers.put(CVC5, cvc5);
    solvers.put(Z3, z3);
  }

  void disableUNSATCoreChecking() {
    isCoreCheckingEnabled = false;
  }
}
