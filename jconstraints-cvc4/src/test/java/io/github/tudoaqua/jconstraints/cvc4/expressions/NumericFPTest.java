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

package io.github.tudoaqua.jconstraints.cvc4.expressions;

import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.NE;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.PLUS;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import io.github.tudoaqua.jconstraints.cvc4.AbstractCVC4Test;
import org.junit.jupiter.api.Test;

public class NumericFPTest extends AbstractCVC4Test {

  @Test
  public void doubleComparisonTest() {
    Constant<Double> c0 = Constant.create(BuiltinTypes.DOUBLE, 0.0);
    Variable<Double> x1 = Variable.create(BuiltinTypes.DOUBLE, "x");
    NumericBooleanExpression expr = NumericBooleanExpression.create(x1, GT, c0);
    NumericBooleanExpression expr2 = NumericBooleanExpression.create(x1, NumericComparator.LT, c0);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));
    assertFalse(expr2.evaluate(val));

    val = new Valuation();
    res = cvc4.solve(expr2, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr2.evaluate(val));
    assertFalse(expr.evaluate(val));
  }

  @Test
  public void castDoubleTest() {
    Constant<Double> c10 = Constant.create(BuiltinTypes.DOUBLE, 1.0);
    Constant<Integer> c0 = Constant.createCasted(BuiltinTypes.SINT32, 0);
    Constant<Double> c00 = Constant.create(BuiltinTypes.DOUBLE, 0.0);
    Variable<Double> x1 = Variable.create(BuiltinTypes.DOUBLE, "x");

    NumericCompound<Double> doublePlus = NumericCompound.create(x1, PLUS, c10);
    NumericBooleanExpression gtDouble = NumericBooleanExpression.create(doublePlus, GT, c00);
    NumericBooleanExpression gtSINT32 =
        NumericBooleanExpression.create(
            CastExpression.create(doublePlus, BuiltinTypes.SINT32), GT, c0);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(gtDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtDouble.evaluate(val));

    val = new Valuation();
    res = cvc4.solve(gtSINT32, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtSINT32.evaluate(val));
  }

  @Test
  public void castIntToDoubleTest() {
    Constant<Double> c10 = Constant.create(BuiltinTypes.DOUBLE, 1.0);
    Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
    Variable<Integer> x1 = Variable.create(BuiltinTypes.SINT32, "x");

    NumericCompound<Integer> plus = NumericCompound.create(x1, PLUS, c1);
    NumericBooleanExpression eqDouble =
        NumericBooleanExpression.create(CastExpression.create(plus, BuiltinTypes.DOUBLE), EQ, c10);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(eqDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(eqDouble.evaluate(val));
  }

  @Test
  public void GreateMaxIntHalfTest() {
    Constant<Double> c = Constant.create(BuiltinTypes.DOUBLE, (double) Integer.MAX_VALUE / 2);
    Variable<Double> x = Variable.create(BuiltinTypes.DOUBLE, "x");
    NumericBooleanExpression gt = NumericBooleanExpression.create(x, GT, c);
    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(gt, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gt.evaluate(val));
  }

  @Test
  public void floatComparisonTest() {
    Constant<Float> c0 = Constant.create(BuiltinTypes.FLOAT, 0.0f);
    Variable<Float> x1 = Variable.create(BuiltinTypes.FLOAT, "x");
    NumericBooleanExpression expr = NumericBooleanExpression.create(x1, GT, c0);
    NumericBooleanExpression expr2 = NumericBooleanExpression.create(x1, NumericComparator.LT, c0);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));
    assertFalse(expr2.evaluate(val));

    val = new Valuation();
    res = cvc4.solve(expr2, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr2.evaluate(val));
    assertFalse(expr.evaluate(val));
  }

  @Test
  public void castFloatTest() {
    Constant<Float> c10 = Constant.create(BuiltinTypes.FLOAT, 1.0f);
    Constant<Integer> c0 = Constant.createCasted(BuiltinTypes.SINT32, 0);
    Constant<Float> c00 = Constant.create(BuiltinTypes.FLOAT, 0.0f);
    Variable<Float> x1 = Variable.create(BuiltinTypes.FLOAT, "x");

    NumericCompound<Float> doublePlus = NumericCompound.create(x1, PLUS, c10);
    NumericBooleanExpression gtDouble = NumericBooleanExpression.create(doublePlus, GT, c00);
    NumericBooleanExpression gtSINT32 =
        NumericBooleanExpression.create(
            CastExpression.create(doublePlus, BuiltinTypes.SINT32), GT, c0);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(gtDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtDouble.evaluate(val));

    val = new Valuation();
    res = cvc4.solve(gtSINT32, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtSINT32.evaluate(val));
  }

  @Test
  public void castIntToFloatTest() {
    Constant<Float> c10 = Constant.create(BuiltinTypes.FLOAT, 1.0f);
    Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
    Variable<Integer> x1 = Variable.create(BuiltinTypes.SINT32, "x");

    NumericCompound<Integer> plus = NumericCompound.create(x1, PLUS, c1);
    NumericBooleanExpression eqDouble =
        NumericBooleanExpression.create(CastExpression.create(plus, BuiltinTypes.FLOAT), EQ, c10);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(eqDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(eqDouble.evaluate(val));
  }

  @Test
  public void GreateMaxIntQuarterTest() {
    Constant<Float> c = Constant.create(BuiltinTypes.FLOAT, (float) Integer.MAX_VALUE / 4);
    Variable<Float> x = Variable.create(BuiltinTypes.FLOAT, "x");
    NumericBooleanExpression gt = NumericBooleanExpression.create(x, GT, c);
    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(gt, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gt.evaluate(val));
  }

  @Test
  public void castLongToDoubleTest() {
    Constant<Double> c10 = Constant.create(BuiltinTypes.DOUBLE, 1.0);
    Constant<Long> c1 = Constant.create(BuiltinTypes.SINT64, 1L);
    Variable<Long> x1 = Variable.create(BuiltinTypes.SINT64, "x");

    NumericCompound<Long> plus = NumericCompound.create(x1, PLUS, c1);
    NumericBooleanExpression eqDouble =
        NumericBooleanExpression.create(CastExpression.create(plus, BuiltinTypes.DOUBLE), EQ, c10);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(eqDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(eqDouble.evaluate(val));
  }

  @Test
  public void castDoubleToLongTest() {
    Constant<Double> c10 = Constant.create(BuiltinTypes.DOUBLE, 1.0);
    Constant<Long> c0 = Constant.create(BuiltinTypes.SINT64, 0L);
    Constant<Double> c00 = Constant.create(BuiltinTypes.DOUBLE, 0.0);
    Variable<Double> x1 = Variable.create(BuiltinTypes.DOUBLE, "x");

    NumericCompound<Double> doublePlus = NumericCompound.create(x1, PLUS, c10);
    NumericBooleanExpression gtDouble = NumericBooleanExpression.create(doublePlus, GT, c00);
    NumericBooleanExpression gtSINT32 =
        NumericBooleanExpression.create(
            CastExpression.create(doublePlus, BuiltinTypes.SINT64), GT, c0);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(gtDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtDouble.evaluate(val));

    val = new Valuation();
    res = cvc4.solve(gtSINT32, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtSINT32.evaluate(val));
  }

  @Test
  public void castLongToFloatTest() {
    Constant<Float> c10 = Constant.create(BuiltinTypes.FLOAT, 1.0f);
    Constant<Long> c1 = Constant.create(BuiltinTypes.SINT64, 1L);
    Variable<Long> x1 = Variable.create(BuiltinTypes.SINT64, "x");

    NumericCompound<Long> plus = NumericCompound.create(x1, PLUS, c1);
    NumericBooleanExpression eqDouble =
        NumericBooleanExpression.create(CastExpression.create(plus, BuiltinTypes.FLOAT), EQ, c10);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(eqDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(eqDouble.evaluate(val));
  }

  @Test
  public void castFloatToLongTest() {
    Constant<Float> c10 = Constant.create(BuiltinTypes.FLOAT, 1.0f);
    Constant<Long> c0 = Constant.createCasted(BuiltinTypes.SINT64, 0L);
    Constant<Float> c00 = Constant.create(BuiltinTypes.FLOAT, 0.0f);
    Variable<Float> x1 = Variable.create(BuiltinTypes.FLOAT, "x");

    NumericCompound<Float> doublePlus = NumericCompound.create(x1, PLUS, c10);
    NumericBooleanExpression gtDouble = NumericBooleanExpression.create(doublePlus, GT, c00);
    NumericBooleanExpression gtSINT32 =
        NumericBooleanExpression.create(
            CastExpression.create(doublePlus, BuiltinTypes.SINT64), GT, c0);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(gtDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtDouble.evaluate(val));

    val = new Valuation();
    res = cvc4.solve(gtSINT32, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtSINT32.evaluate(val));
  }

  @Test
  public void notEqualsTest() {
    Variable<Double> x1 = Variable.create(BuiltinTypes.DOUBLE, "x");
    Variable<Double> x2 = Variable.create(BuiltinTypes.DOUBLE, "y");
    NumericBooleanExpression neExpr = NumericBooleanExpression.create(x1, NE, x2);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(neExpr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(neExpr.evaluate(val));
  }

  @Test
  public void castDoubleToFloatTest() {
    Variable<Double> x1 = Variable.create(BuiltinTypes.DOUBLE, "x");
    Variable<Float> x2 = Variable.create(BuiltinTypes.FLOAT, "y");
    NumericBooleanExpression neExpr =
        NumericBooleanExpression.create(CastExpression.create(x1, BuiltinTypes.FLOAT), NE, x2);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(neExpr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(neExpr.evaluate(val));
  }

  @Test
  public void castFloatToDoubleTest() {
    Variable<Float> x1 = Variable.create(BuiltinTypes.FLOAT, "x");
    Variable<Double> x2 = Variable.create(BuiltinTypes.DOUBLE, "y");
    NumericBooleanExpression neExpr =
        NumericBooleanExpression.create(CastExpression.create(x1, BuiltinTypes.DOUBLE), NE, x2);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(neExpr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(neExpr.evaluate(val));
  }

  @Test
  public void floatSubtest() {
    Variable<Float> x1 = Variable.create(BuiltinTypes.FLOAT, "x");
    Constant<Float> c1 = Constant.create(BuiltinTypes.FLOAT, 119.0f);
    Constant<Double> c00 = Constant.create(BuiltinTypes.DOUBLE, 0.0);
    NumericBooleanExpression neExpr =
        NumericBooleanExpression.create(
            CastExpression.create(
                NumericCompound.create(x1, NumericOperator.MINUS, c1), BuiltinTypes.DOUBLE),
            EQ,
            c00);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(neExpr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(neExpr.evaluate(val));
  }

  @Test
  public void floatConstTest() {
    Variable<Float> x1 = Variable.create(BuiltinTypes.FLOAT, "x");
    Constant<Float> c1 = Constant.create(BuiltinTypes.FLOAT, 119.0f);
    NumericBooleanExpression expr = NumericBooleanExpression.create(x1, EQ, c1);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));
  }

  @Test
  public void doubleConstTest() {
    Variable<Double> x1 = Variable.create(BuiltinTypes.DOUBLE, "x");
    Constant<Double> c1 = Constant.create(BuiltinTypes.DOUBLE, 119.0);
    NumericBooleanExpression expr = NumericBooleanExpression.create(x1, EQ, c1);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));
  }

  @Test
  public void floatEqualsTest() {
    Variable<Float> x1 = Variable.create(BuiltinTypes.FLOAT, "x");
    Variable<Float> c1 = Variable.create(BuiltinTypes.FLOAT, "y");
    NumericBooleanExpression expr =
        NumericBooleanExpression.create(x1, EQ, NumericCompound.create(x1, PLUS, c1));

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));
  }

  @Test
  public void unaryMinusTest() {
    Variable<Float> var = Variable.create(BuiltinTypes.FLOAT, "x");
    UnaryMinus<Float> um = UnaryMinus.create(var);
    NumericBooleanExpression nbe =
        NumericBooleanExpression.create(um, GT, Constant.create(BuiltinTypes.FLOAT, 5.0f));

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(nbe, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(nbe.evaluate(val));
  }
}
