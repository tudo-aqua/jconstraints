/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2025 The jConstraints Authors
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
import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.*;

public class SMTProblem {
  public List<Expression<Boolean>> assertions;
  public Set<Variable<?>> variables;
  public Map<String, Function<?>> functions;

  public SMTProblem() {
    assertions = new ArrayList<>();
    variables = new HashSet<>();
    functions = new HashMap<>();
  }

  public void addAssertion(Expression<Boolean> expr) {
    assertions.add(expr);
  }

  public void addVariable(Variable<?> var) {
    variables.add(var);
  }

  public Expression<Boolean> getAllAssertionsAsConjunction() {
    return ExpressionUtil.and(assertions);
  }

  public SolverContext addProblemToContext(SolverContext ctx) {
    for (Expression<Boolean> expr : assertions) {
      ctx.add(expr);
    }
    return ctx;
  }

  public void addFunction(Function<?> fct) throws SMTLIBParserException {
    if (this.functions.containsKey(fct.getName()))
      throw new SMTLIBParserException(
          "An SMT Problem must not define twice the same function namen.");
    this.functions.put(fct.getName(), fct);
  }
}
