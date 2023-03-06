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

package tools.aqua.jconstraints.benchmarktest.benchmarks;

import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.SAT;
import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.UNSAT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GE;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.LE;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.LT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.NE;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.DIV;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.MINUS;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.MOD;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.MUL;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.PLUS;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.REM;
import static gov.nasa.jpf.constraints.types.BuiltinTypes.SINT32;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.types.BuiltinTypes.SInt32Type;

/**
 * Contains {@link TestCase}s for the handling of various operations on the {@link SInt32Type}
 * containing only {@link Constant}s.
 */
public enum SINT32ConstantTestExpressions implements TestCase {
  SINT32_CONST_EQ_PLUS_SAT(expressionOf(100, PLUS, 2, EQ, 102), SAT),
  SINT32_CONST_EQ_PLUS_UNSAT(expressionOf(100, PLUS, 2, EQ, 100), UNSAT),
  SINT32_CONST_EQ_MINUS_SAT(expressionOf(100, MINUS, 2, EQ, 98), SAT),
  SINT32_CONST_EQ_MINUS_UNSAT(expressionOf(100, MINUS, 2, EQ, 100), UNSAT),
  SINT32_CONST_EQ_MUL_SAT(expressionOf(100, MUL, -2, EQ, -200), SAT),
  SINT32_CONST_EQ_MUL_UNSAT(expressionOf(100, MUL, 2, EQ, 100), UNSAT),
  SINT32_CONST_EQ_DIV_SAT(expressionOf(100, DIV, 2, EQ, 50), SAT),
  SINT32_CONST_EQ_DIV_UNSAT(expressionOf(100, DIV, 2, EQ, 100), UNSAT),
  SINT32_CONST_EQ_MOD_SAT(expressionOf(-101, MOD, 2, EQ, 1), SAT),
  SINT32_CONST_EQ_MOD_UNSAT(expressionOf(-101, MOD, 2, EQ, -1), UNSAT),
  SINT32_CONST_EQ_REMPOSITIVE_SAT(expressionOf(100, REM, 2, EQ, 0), SAT),
  SINT32_CONST_EQ_REMPOSITIVE_UNSAT(expressionOf(100, REM, 2, EQ, 1), UNSAT),
  SINT32_CONST_EQ_REMNEGATIVE_SAT(expressionOf(-101, REM, 2, EQ, -1), SAT),
  SINT32_CONST_EQ_REMNEGATIVE_UNSAT(expressionOf(-101, REM, 2, EQ, 1), UNSAT),

  SINT32_CONST_NE_PLUS_SAT(expressionOf(100, PLUS, 2, NE, 100), SAT),
  SINT32_CONST_NE_PLUS_UNSAT(expressionOf(100, PLUS, 2, NE, 102), UNSAT),
  SINT32_CONST_NE_MINUS_SAT(expressionOf(100, MINUS, 2, NE, 100), SAT),
  SINT32_CONST_NE_MINUS_UNSAT(expressionOf(100, MINUS, 2, NE, 98), UNSAT),
  SINT32_CONST_NE_MUL_SAT(expressionOf(100, MUL, -2, NE, 100), SAT),
  SINT32_CONST_NE_MUL_UNSAT(expressionOf(100, MUL, 2, NE, 200), UNSAT),
  SINT32_CONST_NE_DIV_SAT(expressionOf(100, DIV, 2, NE, 100), SAT),
  SINT32_CONST_NE_DIV_UNSAT(expressionOf(100, DIV, 2, NE, 50), UNSAT),
  SINT32_CONST_NE_MOD_SAT(expressionOf(-101, MOD, 2, NE, -1), SAT),
  SINT32_CONST_NE_MOD_UNSAT(expressionOf(-101, MOD, 2, NE, 1), UNSAT),
  SINT32_CONST_NE_REMPOSITIVE_SAT(expressionOf(100, REM, 2, NE, 1), SAT),
  SINT32_CONST_NE_REMPOSITIVE_UNSAT(expressionOf(100, REM, 2, NE, 0), UNSAT),
  SINT32_CONST_NE_REMNEGATIVE_SAT(expressionOf(-101, REM, 2, NE, 1), SAT),
  SINT32_CONST_NE_REMNEGATIVE_UNSAT(expressionOf(-101, REM, 2, NE, -1), UNSAT),

  SINT32_CONST_LT_PLUS_SAT(expressionOf(100, PLUS, 2, LT, 200), SAT),
  SINT32_CONST_LT_PLUS_UNSAT(expressionOf(100, PLUS, 2, LT, 102), UNSAT),
  SINT32_CONST_LT_MINUS_SAT(expressionOf(100, MINUS, 2, LT, 100), SAT),
  SINT32_CONST_LT_MINUS_UNSAT(expressionOf(100, MINUS, 2, LT, 98), UNSAT),
  SINT32_CONST_LT_MUL_SAT(expressionOf(100, MUL, 2, LT, 202), SAT),
  SINT32_CONST_LT_MUL_UNSAT(expressionOf(100, MUL, 2, LT, 200), UNSAT),
  SINT32_CONST_LT_DIV_SAT(expressionOf(100, DIV, 2, LT, 100), SAT),
  SINT32_CONST_LT_DIV_UNSAT(expressionOf(100, DIV, 2, LT, 50), UNSAT),
  SINT32_CONST_LT_MOD_SAT(expressionOf(-101, MOD, 2, LT, 2), SAT),
  SINT32_CONST_LT_MOD_UNSAT(expressionOf(-101, MOD, 2, LT, 0), UNSAT),
  SINT32_CONST_LT_REMPOSITIVE_SAT(expressionOf(100, REM, 2, LT, 100), SAT),
  SINT32_CONST_LT_REMPOSITIVE_UNSAT(expressionOf(100, REM, 2, LT, 0), UNSAT),
  SINT32_CONST_LT_REMNEGATIVE_SAT(expressionOf(-101, REM, 2, LT, 0), SAT),
  SINT32_CONST_LT_REMNEGATIVE_UNSAT(expressionOf(-101, REM, 2, LT, -1), UNSAT),

  SINT32_CONST_LE_PLUS_SAT(expressionOf(100, PLUS, 2, LE, 102), SAT),
  SINT32_CONST_LE_PLUS_UNSAT(expressionOf(100, PLUS, 2, LE, 100), UNSAT),
  SINT32_CONST_LE_MINUS_SAT(expressionOf(100, MINUS, 2, LE, 100), SAT),
  SINT32_CONST_LE_MINUS_UNSAT(expressionOf(100, MINUS, 2, LE, 2), UNSAT),
  SINT32_CONST_LE_MUL_SAT(expressionOf(100, MUL, 2, LE, 202), SAT),
  SINT32_CONST_LE_MUL_UNSAT(expressionOf(100, MUL, 2, LE, 100), UNSAT),
  SINT32_CONST_LE_DIV_SAT(expressionOf(100, DIV, 2, LE, 100), SAT),
  SINT32_CONST_LE_DIV_UNSAT(expressionOf(100, DIV, 2, LE, 2), UNSAT),
  SINT32_CONST_LE_MOD_SAT(expressionOf(-101, MOD, 2, LE, 2), SAT),
  SINT32_CONST_LE_MOD_UNSAT(expressionOf(-101, MOD, 2, LE, 0), UNSAT),
  SINT32_CONST_LE_REMPOSITIVE_SAT(expressionOf(100, REM, 2, LE, 100), SAT),
  SINT32_CONST_LE_REMPOSITIVE_UNSAT(expressionOf(100, REM, 2, LE, -1), UNSAT),
  SINT32_CONST_LE_REMNEGATIVE_SAT(expressionOf(-101, REM, 2, LE, 0), SAT),
  SINT32_CONST_LE_REMNEGATIVE_UNSAT(expressionOf(-101, REM, 2, LE, -2), UNSAT),

  SINT32_CONST_GT_PLUS_SAT(expressionOf(100, PLUS, 2, GT, 100), SAT),
  SINT32_CONST_GT_PLUS_UNSAT(expressionOf(100, PLUS, 2, GT, 102), UNSAT),
  SINT32_CONST_GT_MINUS_SAT(expressionOf(100, MINUS, 2, GT, 2), SAT),
  SINT32_CONST_GT_MINUS_UNSAT(expressionOf(100, MINUS, 2, GT, 98), UNSAT),
  SINT32_CONST_GT_MUL_SAT(expressionOf(100, MUL, 2, GT, 100), SAT),
  SINT32_CONST_GT_MUL_UNSAT(expressionOf(100, MUL, 2, GT, 200), UNSAT),
  SINT32_CONST_GT_DIV_SAT(expressionOf(100, DIV, 2, GT, 2), SAT),
  SINT32_CONST_GT_DIV_UNSAT(expressionOf(100, DIV, 2, GT, 50), UNSAT),
  SINT32_CONST_GT_MOD_SAT(expressionOf(-101, MOD, 2, GT, 0), SAT),
  SINT32_CONST_GT_MOD_UNSAT(expressionOf(-101, MOD, 2, GT, 2), UNSAT),
  SINT32_CONST_GT_REMPOSITIVE_SAT(expressionOf(100, REM, 2, GT, -1), SAT),
  SINT32_CONST_GT_REMPOSITIVE_UNSAT(expressionOf(100, REM, 2, GT, 100), UNSAT),
  SINT32_CONST_GT_REMNEGATIVE_SAT(expressionOf(-101, REM, 2, GT, -2), SAT),
  SINT32_CONST_GT_REMNEGATIVE_UNSAT(expressionOf(-101, REM, 2, GT, 0), UNSAT),

  SINT32_CONST_GE_PLUS_SAT(expressionOf(100, PLUS, 2, GE, 102), SAT),
  SINT32_CONST_GE_PLUS_UNSAT(expressionOf(100, PLUS, 2, GE, 200), UNSAT),
  SINT32_CONST_GE_MINUS_SAT(expressionOf(100, MINUS, 2, GE, 2), SAT),
  SINT32_CONST_GE_MINUS_UNSAT(expressionOf(100, MINUS, 2, GE, 100), UNSAT),
  SINT32_CONST_GE_MUL_SAT(expressionOf(100, MUL, 2, GE, 200), SAT),
  SINT32_CONST_GE_MUL_UNSAT(expressionOf(100, MUL, 2, GE, 300), UNSAT),
  SINT32_CONST_GE_DIV_SAT(expressionOf(100, DIV, 2, GE, 2), SAT),
  SINT32_CONST_GE_DIV_UNSAT(expressionOf(100, DIV, 2, GE, 100), UNSAT),
  SINT32_CONST_GE_MOD_SAT(expressionOf(-101, MOD, 2, GE, 0), SAT),
  SINT32_CONST_GE_MOD_UNSAT(expressionOf(-101, MOD, 2, GE, 2), UNSAT),
  SINT32_CONST_GE_REMPOSITIVE_SAT(expressionOf(100, REM, 2, GE, 0), SAT),
  SINT32_CONST_GE_REMPOSITIVE_UNSAT(expressionOf(100, REM, 2, GE, 2), UNSAT),
  SINT32_CONST_GE_REMNEGATIVE_SAT(expressionOf(-101, REM, 2, GE, -1), SAT),
  SINT32_CONST_GE_REMNEGATIVE_UNSAT(expressionOf(-101, REM, 2, GE, 0), UNSAT),

  SINT32_CONST_OVERFLOW_SAT(expressionOf(Integer.MAX_VALUE, PLUS, 1, EQ, Integer.MIN_VALUE), SAT);

  private static NumericBooleanExpression expressionOf(
      int operand1,
      NumericOperator operator,
      int operand2,
      NumericComparator comparator,
      int compareValue) {
    return NumericBooleanExpression.create(
        NumericCompound.create(
            Constant.create(SINT32, operand1), operator, Constant.create(SINT32, operand2)),
        comparator,
        Constant.create(SINT32, compareValue));
  }

  private final Expression<Boolean> test;
  private final Result expected;

  SINT32ConstantTestExpressions(Expression<Boolean> expr, Result result) {
    this.test = expr;
    this.expected = result;
  }

  @Override
  public Expression<Boolean> getTest() {
    return this.test;
  }

  @Override
  public Result getExpectedResult() {
    return this.expected;
  }

  @Override
  public String getName() {
    return this.toString();
  }
}
