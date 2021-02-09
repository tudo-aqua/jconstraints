/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
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

package gov.nasa.jpf.constraints.smtlibUtility;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class SMTProblem {
  public List<Expression<Boolean>> assertions;
  public Set<Variable<?>> variables;

  public SMTProblem() {
    assertions = new ArrayList<>();
    variables = new HashSet<>();
  }

  public void addAssertion(Expression<Boolean> expr) {
    assertions.add(expr);
  }

  public void addVariable(Variable var) {
    variables.add(var);
  }

  public Expression<Boolean> getAllAssertionsAsConjunction() {
    return ExpressionUtil.and(assertions);
  }

  public SolverContext addProblemToContext(SolverContext ctx) {
    for (Expression expr : assertions) {
      ctx.add(expr);
    }
    return ctx;
  }
}
