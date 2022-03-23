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

package gov.nasa.jpf.constraints.simplifiers;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.math.BigInteger;
import java.util.Set;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("simplifiers")
public class ReplaceArithmeticExpressionTest {
  private final Expression<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  private final Expression<Integer> x1 = Variable.create(BuiltinTypes.SINT32, "x1");

  private final Expression<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
  private final Expression<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);
  private final Expression<Integer> c5 = Constant.create(BuiltinTypes.SINT32, 5);
  private final Expression<Boolean> xInit =
      NumericBooleanExpression.create(x, NumericComparator.LT, c2);

  private final Expression<Boolean> update =
      NumericBooleanExpression.create(
          x1, NumericComparator.EQ, NumericCompound.create(x, NumericOperator.PLUS, c1));
  private final Expression<Boolean> guardCheck =
      NumericBooleanExpression.create(x1, NumericComparator.LT, c5);
  private final Expression<Boolean> completeUpdate = ExpressionUtil.and(xInit, update, guardCheck);

  private final Expression<Boolean> guardReplaced =
      NumericBooleanExpression.create(
          NumericCompound.create(x, NumericOperator.PLUS, c1), NumericComparator.LT, c5);
  private final Variable<Integer> x2 = Variable.create(BuiltinTypes.SINT32, "x2");
  private final Constant<Integer> c4 = Constant.create(BuiltinTypes.SINT32, 20);

  private final Expression<Boolean> furtherUpdate =
      NumericBooleanExpression.create(x2, NumericComparator.EQ, x1);
  private final Expression<Boolean> checkOnX2 =
      NumericBooleanExpression.create(x2, NumericComparator.GE, c4);
  private final Expression<Boolean> all =
      ExpressionUtil.and(completeUpdate, furtherUpdate, checkOnX2);

  private final Expression<Boolean> x2GuardReplacement =
      NumericBooleanExpression.create(
          NumericCompound.create(x, NumericOperator.PLUS, c1), NumericComparator.GE, c4);

  @Test
  public void simpleReplacementTest() {
    Expression<Boolean> expected = ExpressionUtil.and(xInit, guardReplaced);

    assertEquals(NumericSimplificationUtil.simplify(completeUpdate), expected);
  }

  @Test
  public void noReplacementTest() {
    Expression<Boolean> anotherAssignment =
        NumericBooleanExpression.create(x1, NumericComparator.EQ, c5);
    Expression<Boolean> expected = ExpressionUtil.and(completeUpdate, anotherAssignment);
    assertEquals(NumericSimplificationUtil.simplify(expected), expected);
  }

  @Test
  public void replacementInChainTest() {
    Expression<Boolean> expected = ExpressionUtil.and(xInit, guardReplaced, x2GuardReplacement);
    assertEquals(NumericSimplificationUtil.simplify(all), expected);
  }

  @Test
  public void replacementInManipulatedChainTest() {
    Variable<Integer> x3 = Variable.create(BuiltinTypes.SINT32, "x3");
    Expression<Boolean> extension =
        NumericBooleanExpression.create(
            x3, NumericComparator.EQ, NumericCompound.create(x2, NumericOperator.PLUS, c5));

    Expression<Boolean> checkX3 = NumericBooleanExpression.create(x3, NumericComparator.LT, c4);
    Expression<Boolean> toSimplify = ExpressionUtil.and(all, checkX3, extension);
    Expression simplified = NumericSimplificationUtil.simplify(toSimplify);

    Set<Variable<?>> variables = ExpressionUtil.freeVariables(simplified);

    assertFalse(variables.contains(x2));
    assertFalse(variables.contains(x1));
    assertFalse(variables.contains(x3));
  }

  @Test
  public void replacementWithNotInExpression() {
    /*
     * Is it always allowed to convert a not (a == b) into (a != b)?
     * This might simplify the implementation of this test case further.
     * TODO: Investigate negation push into the theory.
     */
    Constant<BigInteger> c0 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(0));
    Constant<BigInteger> c4 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(4));
    Constant<BigInteger> c5 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(5));
    Constant<BigInteger> c12 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(12));
    Constant<BigInteger> c42 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(42));
    Variable<BigInteger> y1 = Variable.create(BuiltinTypes.INTEGER, "y1");
    Variable<BigInteger> x1 = Variable.create(BuiltinTypes.INTEGER, "x1");
    Variable<BigInteger> y2 = Variable.create(BuiltinTypes.INTEGER, "y2");
    Variable<BigInteger> x2 = Variable.create(BuiltinTypes.INTEGER, "x2");

    Expression<Boolean> exprEQ = NumericBooleanExpression.create(y1, NumericComparator.EQ, c5);
    Expression<Boolean> lt = NumericBooleanExpression.create(x1, NumericComparator.LT, c0);
    Expression<Boolean> negatedEQ =
        Negation.create(NumericBooleanExpression.create(x1, NumericComparator.EQ, c42));

    Expression<Boolean> exprEQ2 = NumericBooleanExpression.create(x2, NumericComparator.EQ, c4);
    Expression<Boolean> exprEQ3 = NumericBooleanExpression.create(y2, NumericComparator.EQ, c12);

    Expression<Boolean> problem = ExpressionUtil.and(exprEQ, lt, negatedEQ, exprEQ2, exprEQ3);

    Expression res = NumericSimplificationUtil.simplify(problem);
    assertEquals(res, PropositionalCompound.create(lt, LogicalOperator.AND, negatedEQ));
  }
}
