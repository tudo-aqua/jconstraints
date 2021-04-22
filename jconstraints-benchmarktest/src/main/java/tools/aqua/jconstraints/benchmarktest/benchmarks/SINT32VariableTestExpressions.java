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
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.types.BuiltinTypes.SInt32Type;

// TODO Variablenbelegung
/**
 * Contains {@link TestCase}s for the handling of various operations on the {@link SInt32Type}
 * containing {@link Constant}s and {@link Variable}s.
 */
public enum SINT32VariableTestExpressions implements TestCase {
  SINT32_VAR_EQ_PLUS_SAT(expressionOf(PLUS, 2, EQ, 102), SAT),
  SINT32_VAR_EQ_MINUS_SAT(expressionOf(MINUS, 2, EQ, 98), SAT),
  SINT32_VAR_EQ_MULT_SAT(expressionOf(MUL, 2, EQ, 200), SAT),
  SINT32_VAR_EQ_MULT_UNSAT(expressionOf(MUL, 2, EQ, 1), UNSAT),
  SINT32_VAR_EQ_DIV_SAT(expressionOf(DIV, 2, EQ, 50), SAT),
  SINT32_VAR_EQ_DIV_UNSAT(expressionOf(DIV, 2, EQ, Integer.MAX_VALUE), UNSAT),
  SINT32_VAR_EQ_REM_SAT(expressionOf(REM, 2, EQ, -1), SAT),
  SINT32_VAR_EQ_REM_UNSAT(expressionOf(REM, 2, EQ, 100), UNSAT),
  SINT32_VAR_EQ_MOD_SAT(expressionOf(MOD, 2, EQ, 1), SAT),
  SINT32_VAR_EQ_MOD_UNSAT(expressionOf(MOD, 2, EQ, -1), UNSAT),

  SINT32_VAR_NE_PLUS_SAT(expressionOf(PLUS, 2, NE, 100), SAT),
  SINT32_VAR_NE_MINUS_SAT(expressionOf(MINUS, 2, NE, 100), SAT),
  SINT32_VAR_NE_MULT_SAT(expressionOf(MUL, 2, NE, 200), SAT),
  SINT32_VAR_NE_DIV_SAT(expressionOf(DIV, 0, NE, 100), SAT),
  SINT32_VAR_NE_REM_SAT(expressionOf(REM, 2, NE, 1), SAT),
  SINT32_VAR_NE_MOD_SAT(expressionOf(MOD, 2, NE, 1), SAT),

  SINT32_VAR_LT_PLUS_SAT(expressionOf(PLUS, 2, LT, 100), SAT),
  SINT32_VAR_LT_MINUS_SAT(expressionOf(MINUS, 2, LT, 100), SAT),
  SINT32_VAR_LT_MULT_SAT(expressionOf(MUL, 2, LT, 200), SAT),
  SINT32_VAR_LT_DIV_SAT(expressionOf(DIV, 0, LT, 100), SAT),
  SINT32_VAR_LT_REM_SAT(expressionOf(REM, 2, LT, 1), SAT),
  SINT32_VAR_LT_MOD_SAT(expressionOf(MOD, 2, LT, 1), SAT),
  SINT32_VAR_LT_MOD_UNSAT(expressionOf(MOD, 2, LT, 0), UNSAT),

  SINT32_VAR_LE_PLUS_SAT(expressionOf(PLUS, 2, LE, 100), SAT),
  SINT32_VAR_LE_MINUS_SAT(expressionOf(MINUS, 2, LE, 100), SAT),
  SINT32_VAR_LE_MULT_SAT(expressionOf(MUL, 2, LE, 200), SAT),
  SINT32_VAR_LE_DIV_SAT(expressionOf(DIV, 0, LE, 100), SAT),
  SINT32_VAR_LE_REM_SAT(expressionOf(REM, 2, LE, 1), SAT),
  SINT32_VAR_LE_MOD_SAT(expressionOf(MOD, 2, LE, 1), SAT),
  SINT32_VAR_LE_MOD_UNSAT(expressionOf(MOD, 2, LE, -1), UNSAT),

  SINT32_VAR_GT_PLUS_SAT(expressionOf(PLUS, 2, GT, 100), SAT),
  SINT32_VAR_GT_MINUS_SAT(expressionOf(MINUS, 2, GT, 100), SAT),
  SINT32_VAR_GT_MULT_SAT(expressionOf(MUL, 2, GT, 200), SAT),
  SINT32_VAR_GT_DIV_SAT(expressionOf(DIV, 2, GT, 100), SAT),
  SINT32_VAR_GT_DIV_UNSAT(expressionOf(DIV, 2, GT, Integer.MAX_VALUE), UNSAT),
  SINT32_VAR_GT_REM_SAT(expressionOf(REM, 2, GT, 0), SAT),
  SINT32_VAR_GT_REM_UNSAT(expressionOf(REM, 2, GT, 1), UNSAT),
  SINT32_VAR_GT_MOD_SAT(expressionOf(MOD, 2, GT, 0), SAT),
  SINT32_VAR_GT_MOD_UNSAT(expressionOf(MOD, 2, GT, 1), UNSAT),

  SINT32_VAR_GE_PLUS_SAT(expressionOf(PLUS, 2, GE, 100), SAT),
  SINT32_VAR_GE_MINUS_SAT(expressionOf(MINUS, 2, GE, 100), SAT),
  SINT32_VAR_GE_MULT_SAT(expressionOf(MUL, 2, GE, 200), SAT),
  SINT32_VAR_GE_DIV_SAT(expressionOf(DIV, 2, GE, 100), SAT),
  SINT32_VAR_GE_DIV_UNSAT(expressionOf(DIV, 0, GE, 100), UNSAT),
  SINT32_VAR_GE_REM_SAT(expressionOf(REM, 2, GE, 1), SAT),
  SINT32_VAR_GE_REM_UNSAT(expressionOf(REM, 2, GE, 100), UNSAT),
  SINT32_VAR_GE_MOD_SAT(expressionOf(MOD, 2, GE, 0), SAT),
  SINT32_VAR_GE_MOD_UNSAT(expressionOf(MOD, 2, GE, 100), UNSAT),

  SINT32_VAR_OVERFLOW_SAT(expressionOf(PLUS, 1, EQ, Integer.MIN_VALUE), SAT);

  private static NumericBooleanExpression expressionOf(
      NumericOperator operator, int operand2, NumericComparator comparator, int compareValue) {
    return NumericBooleanExpression.create(
        NumericCompound.create(
            Variable.create(SINT32, "_int0"), operator, Constant.create(SINT32, operand2)),
        comparator,
        Constant.create(SINT32, compareValue));
  }

  private final Expression<Boolean> test;
  private final Result expected;

  SINT32VariableTestExpressions(Expression<Boolean> expr, Result result) {
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
