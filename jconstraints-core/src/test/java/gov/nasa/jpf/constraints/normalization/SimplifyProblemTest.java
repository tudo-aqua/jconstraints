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
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("normalization")
public class SimplifyProblemTest {

  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Variable<Integer> y = Variable.create(BuiltinTypes.SINT32, "y");
  Variable<Boolean> b1 = Variable.create(BuiltinTypes.BOOL, "b1");
  Variable<Boolean> b2 = Variable.create(BuiltinTypes.BOOL, "b2");

  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);

  Expression<Boolean> e2 = NumericBooleanExpression.create(y, NumericComparator.LE, c2);
  Expression<Boolean> e3 = NumericBooleanExpression.create(x, NumericComparator.GE, c1);

  Constant<Boolean> top = Constant.create(BuiltinTypes.BOOL, Boolean.TRUE);
  Constant<Boolean> bottom = Constant.create(BuiltinTypes.BOOL, Boolean.FALSE);

  @Test
  public void quantifierSimplificationTest1() {
    List<Variable<?>> bound = new ArrayList<Variable<?>>();
    bound.add(x);
    bound.add(y);
    bound.add(b1);
    bound.add(b2);
    Expression<Boolean> quantified =
        PropositionalCompound.create(
            QuantifierExpression.create(Quantifier.EXISTS, bound, e3), LogicalOperator.OR, e2);
    Expression<Boolean> simplified1 = NormalizationUtil.simplifyProblem(quantified);

    List<Variable<?>> boundExp = new ArrayList<Variable<?>>();
    boundExp.add(x);
    Expression<Boolean> expected =
        PropositionalCompound.create(
            QuantifierExpression.create(Quantifier.EXISTS, boundExp, e3), LogicalOperator.OR, e2);

    assertEquals(simplified1, expected);
  }

  @Test
  public void quantifierSimplificationTest2() {
    List<Variable<?>> bound = new ArrayList<Variable<?>>();
    bound.add(x);
    Expression<Boolean> quantified =
        PropositionalCompound.create(
            QuantifierExpression.create(Quantifier.FORALL, bound, e2), LogicalOperator.OR, e2);
    Expression<Boolean> simplified1 = NormalizationUtil.simplifyProblem(quantified);

    Expression<Boolean> expected = e2;

    assertEquals(simplified1, expected);
  }

  @Test
  public void equalityTest1() {
    Expression<Boolean> equal = PropositionalCompound.create(e2, LogicalOperator.EQUIV, e2);
    Expression<Boolean> simplified1 = NormalizationUtil.simplifyProblem(equal);

    assertEquals(simplified1, top);
  }

  @Test
  public void equalityTest2() {
    Expression<Boolean> equal = PropositionalCompound.create(e2, LogicalOperator.EQUIV, top);
    Expression<Boolean> simplified1 = NormalizationUtil.simplifyProblem(equal);

    assertEquals(simplified1, e2);
  }

  @Test
  public void equalityTest3() {
    Expression<Boolean> equal = PropositionalCompound.create(bottom, LogicalOperator.EQUIV, e2);
    Expression<Boolean> simplified1 = NormalizationUtil.simplifyProblem(equal);

    assertEquals(simplified1, Negation.create(e2));
  }

  @Test
  public void contradictionTest1() {
    Expression<Boolean> contra =
        PropositionalCompound.create(e2, LogicalOperator.AND, Negation.create(e2));
    Expression<Boolean> simplified1 = NormalizationUtil.simplifyProblem(contra);

    assertEquals(simplified1, bottom);
  }

  @Test
  public void tautologyTest1() {
    Expression<Boolean> tautology =
        PropositionalCompound.create(e2, LogicalOperator.OR, Negation.create(e2));
    Expression<Boolean> simplified1 = NormalizationUtil.simplifyProblem(tautology);

    assertEquals(simplified1, top);
  }
}
