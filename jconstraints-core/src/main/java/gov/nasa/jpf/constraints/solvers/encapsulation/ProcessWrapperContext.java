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

package gov.nasa.jpf.constraints.solvers.encapsulation;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.solvers.datastructures.ExpressionStack;
import java.util.List;

public class ProcessWrapperContext extends SolverContext implements UNSATCoreSolver {

  private final ProcessWrapperSolver solver;
  private ExpressionStack stack = new ExpressionStack();

  public ProcessWrapperContext(String name) {
    solver = new ProcessWrapperSolver(name);
  }

  public ProcessWrapperContext(String name, String javaBinary) {
    solver = new ProcessWrapperSolver(name, javaBinary);
  }

  public String getName() {
    return solver.getName();
  }

  @Override
  public void push() {
    stack.push();
  }

  @Override
  public void pop(int n) {
    stack.pop(n);
  }

  @Override
  public Result solve(Valuation val) {
    List<Expression<Boolean>> test = stack.getCurrentExpression();
    Result res = solver.solve(test, val, 0);
    //    if (res.equals(Result.SAT)) {
    //      assert (Boolean) test.evaluate(val);
    //    }
    return res;
  }

  @Override
  public void add(List<Expression<Boolean>> expressions) {
    stack.add(expressions);
  }

  @Override
  public void dispose() {
    stack = new ExpressionStack();
  }

  @Override
  public void enableUnsatTracking() {
    solver.enableUnsatTracking();
  }

  @Override
  public void disableUnsatTracking() {
    solver.disableUnsatTracking();
  }

  @Override
  public List<Expression<Boolean>> getUnsatCore() {
    return solver.getUnsatCore();
  }
}
