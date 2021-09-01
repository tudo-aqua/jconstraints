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
package gov.nasa.jpf.constraints.normalization;

import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("normalization")
public class OrderingTest {

  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Variable<Integer> y = Variable.create(BuiltinTypes.SINT32, "y");
  Variable<Boolean> b1 = Variable.create(BuiltinTypes.BOOL, "b1");

  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);
  NumericCompound<Integer> z = NumericCompound.create(c1, NumericOperator.MUL, x);
  NumericCompound<Integer> zOrdered = NumericCompound.create(x, NumericOperator.MUL, c1);
  NumericCompound<Integer> a = NumericCompound.create(c1, NumericOperator.MINUS, x);
  NumericCompound<Integer> d = NumericCompound.create(c1, NumericOperator.DIV, z);

  Expression<Boolean> e1 = NumericBooleanExpression.create(c1, NumericComparator.NE, x);
  Expression<Boolean> e1ordered = NumericBooleanExpression.create(x, NumericComparator.NE, c1);
  Expression<Boolean> e2 = NumericBooleanExpression.create(y, NumericComparator.LE, c2);
  Expression<Boolean> e3 = NumericBooleanExpression.create(c1, NumericComparator.GE, x);
  Expression<Boolean> e4 = NumericBooleanExpression.create(y, NumericComparator.EQ, c2);
  Expression<Boolean> e5 = NumericBooleanExpression.create(c1, NumericComparator.LE, z);
  Expression<Boolean> e6 = NumericBooleanExpression.create(c1, NumericComparator.LT, a);
  Expression<Boolean> e7 = NumericBooleanExpression.create(c1, NumericComparator.GT, z);
  Expression<Boolean> e8 = NumericBooleanExpression.create(c2, NumericComparator.EQ, y);

  Expression<Boolean> con1 = PropositionalCompound.create(e3, LogicalOperator.AND, e4);
  Expression<Boolean> dis2 = PropositionalCompound.create(e1, LogicalOperator.OR, e2);
  Expression<Boolean> con3 = PropositionalCompound.create(e1, LogicalOperator.AND, e1);
  Expression<Boolean> con4 = PropositionalCompound.create(e2, LogicalOperator.AND, b1);
  Expression<Boolean> imply = PropositionalCompound.create(e2, LogicalOperator.IMPLY, b1);

  @Test
  //LE
  public void orderingTest1(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(e2);

    assertEquals(ordered, e2);
  }

  @Test
  //LE
  public void orderingTest2(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(e5);
    NumericCompound<Integer> zOrdered = NumericCompound.create(x, NumericOperator.MUL, c1);
    Expression<Boolean> expected = NumericBooleanExpression.create(zOrdered, NumericComparator.GE, c1);

    assertEquals(ordered, expected);
  }

  @Test
  //GE
  public void orderingTest3(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(NumericBooleanExpression.create(x, NumericComparator.GE, c1));
    Expression<Boolean> expected = NumericBooleanExpression.create(x, NumericComparator.GE, c1);

    assertEquals(ordered, expected);
  }

  @Test
  //GE
  public void orderingTest4(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(con1);
    Expression<Boolean> expected = PropositionalCompound.create(NumericBooleanExpression.create(x, NumericComparator.LE, c1), LogicalOperator.AND, e4);

    assertEquals(ordered, expected);
  }

  @Test
  //NE
  public void orderingTest5(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(dis2);
    Expression<Boolean> expected = PropositionalCompound.create(NumericBooleanExpression.create(x, NumericComparator.NE, c1), LogicalOperator.OR, e2);

    assertEquals(ordered, expected);
  }

  @Test
  //NE
  public void orderingTest6(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(con3);
    Expression<Boolean> expected = PropositionalCompound.create(e1ordered, LogicalOperator.AND, e1ordered);

    assertEquals(ordered, expected);
  }

  @Test
  //EQ
  public void orderingTest7(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(e8);

    assertEquals(ordered, e4);
  }

  @Test
  //EQ
  public void orderingTest8(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(e4);

    assertEquals(ordered, e4);
  }

  @Test
  public void orderingTest9(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(e6);
    Expression<Boolean> expected = NumericBooleanExpression.create(a, NumericComparator.GT, c1);

    assertEquals(ordered, expected);
  }

  @Test
  public void orderingTest10(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(NumericBooleanExpression.create(a, NumericComparator.GE, c1));
    Expression<Boolean> expected = NumericBooleanExpression.create(a, NumericComparator.GE, c1);

    assertEquals(ordered, expected);
  }

  @Test
  public void orderingTest11(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(e7);
    Expression<Boolean> expected = NumericBooleanExpression.create(zOrdered, NumericComparator.LT, c1);

    assertEquals(ordered, expected);
  }

  @Test
  //LE
  public void orderingTest12(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(NumericBooleanExpression.create(zOrdered, NumericComparator.LE, c1));
    Expression<Boolean> expected = NumericBooleanExpression.create(zOrdered, NumericComparator.LE, c1);

    assertEquals(ordered, expected);
  }

  @Test
  public void orderingTest13(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(con4);
    Expression<Boolean> expected = PropositionalCompound.create(b1, LogicalOperator.AND, e2);

    assertEquals(ordered, expected);
  }

  @Test
  public void orderingTest14(){
    Expression<Boolean> ordered = NormalizationUtil.orderProblem(imply);

    assertEquals(ordered, imply);
  }

  @Test
  public void orderingTest15(){
    Expression<Integer> ordered = NormalizationUtil.orderProblem(d);
    Expression<Integer> expected = NumericCompound.create(c1, NumericOperator.DIV, zOrdered);

    assertEquals(ordered, expected);
  }
}


