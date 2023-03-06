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

package statistics.callables;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
import gov.nasa.jpf.constraints.expressions.RegExOperator;
import gov.nasa.jpf.constraints.expressions.RegexOperatorExpression;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import java.util.concurrent.Callable;
import statistics.datastrucutres.BooleanAnswer;

/*
 * This analysis tasks checks, whether an expression contains a Str in Re Expression.
 */
public class StrInReAnalysisTask implements Callable<BooleanAnswer> {

  private final String file;

  public StrInReAnalysisTask(String file) {
    this.file = file;
  }

  public boolean computeAnswer(Expression<Boolean> expression) {
    while (expression instanceof Negation) {
      expression = ((Negation) expression).getNegated();
    }
    if (expression instanceof RegExBooleanExpression) {
      RegExBooleanExpression castedP = (RegExBooleanExpression) expression;
      if ((castedP.getLeft() instanceof Variable || castedP.getLeft() instanceof Constant)
          && castedP.getRight() instanceof RegexOperatorExpression) {
        RegexOperatorExpression roe = (RegexOperatorExpression) castedP.getRight();
        return roe.getOperator().equals(RegExOperator.ALLCHAR);
      }
    }
    return false;
  }

  @Override
  public BooleanAnswer call() throws Exception {
    try {
      SMTProblem problem = SMTLIBParser.parseSMTProgramFromFile(file);
      return new BooleanAnswer(file, problem.assertions.stream().anyMatch(this::computeAnswer));

    } catch (Exception e) {
      System.out.println(
          "Problem parsing: "
              + file
              + " "
              + (e.getMessage() == null ? e.toString() : e.getMessage()));
    }
    return null;
  }
}
