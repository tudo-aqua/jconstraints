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

package gov.nasa.jpf.constraints.expressions;

import static gov.nasa.jpf.constraints.expressions.LogicalOperator.AND;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GT;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.Set;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("expressions")
public class LetExpressionTest {

  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Variable<Integer> x1 = Variable.create(BuiltinTypes.SINT32, "x1");
  Variable<Integer> x2 = Variable.create(BuiltinTypes.SINT32, "x2");
  Constant<Integer> c = Constant.create(BuiltinTypes.SINT32, 5);
  Expression<Boolean> expr = NumericBooleanExpression.create(x, GT, c);
  Constant<Integer> c4 = Constant.create(BuiltinTypes.SINT32, 4);
  LetExpression letExpr = LetExpression.create(x, c4, expr);

  @Test
  public void LetExpressionAcceptsVisitorTest() {
    DummyVisitorForTest visitor = new DummyVisitorForTest();
    assertEquals(letExpr.accept(visitor, false), letExpr);
  }

  @Test
  public void LetExpressionEvaluation1Test() {
    Valuation val1 = new Valuation();
    val1.setValue(x, 6);

    Valuation val2 = new Valuation();
    val2.setValue(x, 4);

    Valuation val3 = new Valuation();
    val3.setValue(x, 6);

    assertTrue(expr.evaluate(val1));
    assertFalse(letExpr.evaluate(val2));
    assertFalse(letExpr.evaluate(val3));
  }

  @Test
  public void flattenLetExpression1Test() {
    Expression<Boolean> expectedOutcome = NumericBooleanExpression.create(c4, GT, c);
    assertEquals(letExpr.flattenLetExpression(), expectedOutcome);
  }

  @Test
  public void flattenLetExpression2Test() {
    Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);
    NumericBooleanExpression partA = NumericBooleanExpression.create(x1, NumericComparator.LE, c4);
    NumericCompound<Integer> replacement = NumericCompound.create(x2, NumericOperator.PLUS, c2);

    LetExpression expr = LetExpression.create(x1, replacement, partA);

    Expression<Boolean> expectedOutcome =
        NumericBooleanExpression.create(replacement, NumericComparator.LE, c4);

    assertEquals(expr.flattenLetExpression(), expectedOutcome);

    Variable<Boolean> x3 = Variable.create(BuiltinTypes.BOOL, "x3");
    Expression<Boolean> expr2 = PropositionalCompound.create(x3, AND, expr);

    Variable<Integer> x4 = Variable.create(BuiltinTypes.SINT32, "x4");
    NumericBooleanExpression replacementB = NumericBooleanExpression.create(x4, GT, c2);
    LetExpression let2 = LetExpression.create(x3, replacementB, expr2);

    Expression<Boolean> expectedOutcome2 =
        PropositionalCompound.create(replacementB, AND, expectedOutcome);

    System.out.println(let2);
    System.out.println(let2.flattenLetExpression());

    assertEquals(let2.flattenLetExpression(), expectedOutcome2);
  }

  @Test
  public void chainedLetExpressionFlattening01Test() {
    NumericCompound<Integer> nc = NumericCompound.create(x, NumericOperator.PLUS, c4);
    NumericBooleanExpression nbe = NumericBooleanExpression.create(x1, EQ, x2);
    LetExpression inner = LetExpression.create(x1, nc, nbe);
    Variable<Integer> x4 = Variable.create(BuiltinTypes.SINT32, "x4");
    LetExpression outter = LetExpression.create(x, x4, inner);
    Expression flattened = outter.flattenLetExpression();
    Set<Variable<?>> vars = ExpressionUtil.freeVariables(flattened);
    assertFalse(vars.contains(x), "the x should be replaced by x4");
    assertFalse(vars.contains(x1), "The x1 should be replaced by the numeric compound");
    assertTrue(vars.contains(x4), "The x4 is very present now");
  }

  @Test
  public void chainedLetExpressionFlattening02Test() {
    Variable<Integer> y = Variable.create(BuiltinTypes.SINT32, "Y");

    NumericCompound<Integer> nc = NumericCompound.create(x, NumericOperator.PLUS, c4);
    NumericBooleanExpression nbe = NumericBooleanExpression.create(x1, EQ, x2);
    LetExpression inner2 = LetExpression.create(y, nc, y);
    LetExpression inner = LetExpression.create(x1, inner2, nbe);
    Variable<Integer> x4 = Variable.create(BuiltinTypes.SINT32, "x4");
    LetExpression outter = LetExpression.create(x, x4, inner);
    Expression flattened = outter.flattenLetExpression();
    Set<Variable<?>> vars = ExpressionUtil.freeVariables(flattened);
    assertFalse(vars.contains(x), "the x should be replaced by x4");
    assertFalse(vars.contains(x1), "The x1 should be replaced by the numeric compound");
    assertFalse(vars.contains(y), "The y should be replaced by the numeric compound");
    assertTrue(vars.contains(x4), "The x4 is very present now");
  }

  @Test
  public void letExpresisonsAndITE01Test() {
    Variable<Integer> X = Variable.create(BuiltinTypes.SINT32, "X");
    Variable<Integer> X1 = Variable.create(BuiltinTypes.SINT32, "X1");
    Variable<Boolean> B = Variable.create(BuiltinTypes.BOOL, "B");
    Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 5);
    IfThenElse<Integer> ite = IfThenElse.create(B, X1, c1);
    NumericBooleanExpression nbe =
        NumericBooleanExpression.create(ite, GT, Constant.create(BuiltinTypes.SINT32, 6));
    LetExpression let = LetExpression.create(X1, X, nbe);
    Expression flat = let.flattenLetExpression();
    assertFalse(flat.toString().contains("X1"), "X1 should be replaced");
  }

  @Test
  public void letExpresisonsAndITE02Test() {
    Variable<Boolean> X = Variable.create(BuiltinTypes.BOOL, "X");
    Variable<Boolean> X1 = Variable.create(BuiltinTypes.BOOL, "X1");
    Variable<Boolean> X2 = Variable.create(BuiltinTypes.BOOL, "X2");
    Variable<Boolean> X3 = Variable.create(BuiltinTypes.BOOL, "X3");
    Variable<Boolean> X4 = Variable.create(BuiltinTypes.BOOL, "X4");
    Variable<Boolean> B = Variable.create(BuiltinTypes.BOOL, "B");
    Variable<Boolean> B2 = Variable.create(BuiltinTypes.BOOL, "B2");
    Variable<Boolean> B3 = Variable.create(BuiltinTypes.BOOL, "B3");
    Variable<Boolean> B4 = Variable.create(BuiltinTypes.BOOL, "B4");
    Variable<Boolean> LetX1 = Variable.create(BuiltinTypes.BOOL, "LetX1");
    Variable<Boolean> LetX2 = Variable.create(BuiltinTypes.BOOL, "?LetX2");
    Variable<Boolean> LetX3 = Variable.create(BuiltinTypes.BOOL, "?LetX1");
    Variable<Boolean> LetX4 = Variable.create(BuiltinTypes.BOOL, "$xLetX1");
    Variable<Boolean> LetX5 = Variable.create(BuiltinTypes.BOOL, "$xLetX5");

    IfThenElse<Boolean> ite = IfThenElse.create(B, X1, X);
    IfThenElse<Boolean> ite2 = IfThenElse.create(B2, X1, LetX1);
    IfThenElse<Boolean> ite3 = IfThenElse.create(B3, X2, X3);
    IfThenElse<Boolean> ite4 = IfThenElse.create(B4, X4, LetX2);
    LetExpression let1 =
        LetExpression.create(LetX4, PropositionalCompound.create(LetX3, AND, LetX5), LetX4);
    LetExpression let2 = LetExpression.create(LetX3, ite4, let1);
    LetExpression let3 = LetExpression.create(LetX2, ite3, let2);
    LetExpression let4 = LetExpression.create(LetX5, ite2, let3);
    LetExpression let5 = LetExpression.create(LetX1, ite, let4);

    Expression flat = let5.flattenLetExpression();
    Set<Variable<?>> vars = ExpressionUtil.freeVariables(flat);
    assertFalse(vars.contains(LetX1));
    assertFalse(vars.contains(LetX2));
    assertFalse(vars.contains(LetX3));
    assertFalse(vars.contains(LetX4));
    assertFalse(vars.contains(LetX5));
  }

  public static class DummyVisitorForTest extends AbstractExpressionVisitor<Expression, Boolean> {

    @Override
    protected Expression defaultVisit(Expression expression, Boolean data) {
      return expression;
    }
  }
}
