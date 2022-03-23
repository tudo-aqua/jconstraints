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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.parser.ParserUtil;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import org.junit.jupiter.api.Test;

public class ExpressionZ3BVTest {

  @Test
  public void expressionTest() throws ImpreciseRepresentationException {
    // construct expression

    Variable<Integer> var_i1 = Variable.create(BuiltinTypes.SINT32, "i1");

    Constant<Integer> const_63 = Constant.create(BuiltinTypes.SINT32, 127);
    Constant<Integer> const_64 = Constant.create(BuiltinTypes.SINT32, 63);

    BitvectorExpression<Integer> and =
        BitvectorExpression.create(const_63, BitvectorOperator.AND, const_64);

    NumericBooleanExpression expr =
        NumericBooleanExpression.create(and, NumericComparator.EQ, var_i1);

    System.out.println(expr);

    // get names

    Set<Variable<?>> vars = new HashSet<>();
    expr.collectFreeVariables(vars);

    // solve

    ConstraintSolver solver = ConstraintSolverFactory.createSolver("z3");

    Valuation val = new Valuation();
    ConstraintSolver.Result result = solver.solve(expr, val);
    System.out.println(result);
    System.out.println(val);

    Variable<Integer> var_i2 = Variable.create(BuiltinTypes.SINT32, "i2");
    Constant<Integer> const_0 = Constant.create(BuiltinTypes.SINT32, 0);
    Expression<Boolean> expr2 =
        new QuantifierExpression(
            Quantifier.FORALL,
            Collections.singletonList(var_i2),
            NumericBooleanExpression.create(
                NumericCompound.create(var_i1, NumericOperator.MUL, var_i2),
                NumericComparator.EQ,
                const_0));

    System.out.println(expr2);

    Valuation val2 = new Valuation();
    result = solver.solve(expr2, val2);
    System.out.println(result);
    System.out.println(val2);

    Constant<Integer> const_max = Constant.create(BuiltinTypes.SINT32, Integer.MAX_VALUE);
    Constant<Integer> const_min = Constant.create(BuiltinTypes.SINT32, Integer.MIN_VALUE);
    Expression<Boolean> expr3 =
        NumericBooleanExpression.create(
            NumericCompound.create(const_max, NumericOperator.PLUS, var_i1),
            NumericComparator.EQ,
            const_min);

    System.out.println(expr3);

    Valuation val3 = new Valuation();
    result = solver.solve(expr3, val3);
    System.out.println(result);
    System.out.println(val3);

    String parseable = ExpressionUtil.toParseableString(expr2);

    System.out.println("Parseable " + parseable);

    // TODO: this fails with a parsing expression
    Expression<Boolean> parsed = ParserUtil.parseLogical(parseable);
    System.out.println(parsed);
  }
}
