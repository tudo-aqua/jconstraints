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
public class IfThenElseRemoverTest {

  Variable<Boolean> b = Variable.create(BuiltinTypes.BOOL, "b");
  Variable<Boolean> b2 = Variable.create(BuiltinTypes.BOOL, "b2");
  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Variable<Integer> y = Variable.create(BuiltinTypes.SINT32, "y");
  Variable<Integer> p = Variable.create(BuiltinTypes.SINT32, "p");
  Variable<Integer> q = Variable.create(BuiltinTypes.SINT32, "q");
  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);
  Expression<Boolean> e1 = NumericBooleanExpression.create(x, NumericComparator.EQ, c1);
  Expression<Boolean> e2 = NumericBooleanExpression.create(x, NumericComparator.EQ, c2);

  Expression<Boolean> iteExpression = IfThenElse.create(b, e1, e2);
  Expression<Boolean> first = PropositionalCompound.create(Negation.create(b), LogicalOperator.OR, e1);
  Expression<Boolean> second = PropositionalCompound.create(b, LogicalOperator.OR, e2);
  Expression<Boolean> iteFree = PropositionalCompound.create(first, LogicalOperator.AND, second);

  Expression<Boolean> nestedIte = PropositionalCompound.create(e1, LogicalOperator.IMPLY, iteExpression);
  Expression<Boolean> iteFree2 = PropositionalCompound.create(e1, LogicalOperator.IMPLY, iteFree);

  @Test
  public void ifThenElseTest() {
    Expression<Boolean> result = NormalizationUtil.eliminateIfThenElse(iteExpression);

    assertEquals(result, iteFree);
  }

  @Test
  public void nestedIfThenElseTest() {
    Expression<Boolean> result = NormalizationUtil.eliminateIfThenElse(nestedIte);

    assertEquals(result, iteFree2);
  }

  @Test
  public void numericIfThenElseTest() {
    Expression<Boolean> compound = NumericBooleanExpression.create(
        IfThenElse.create(b, x, y),
        NumericComparator.EQ,
        NumericCompound.create(
            UnaryMinus.create(c1),
            NumericOperator.PLUS,
            IfThenElse.create(b2, p, q)));

    Expression<Boolean> result = NormalizationUtil.eliminateIfThenElse(compound);

    System.out.println(result);
  }

  @Test
  public void numericIfThenElseTest2() {
    Expression<Boolean> compound = NumericBooleanExpression.create(
        IfThenElse.create(b, IfThenElse.create(b, x, y), y),
        NumericComparator.EQ,
        NumericCompound.create(
            IfThenElse.create(b2, p, q),
            NumericOperator.PLUS,
            IfThenElse.create(b2, p, q)));

    Expression<Boolean> result = NormalizationUtil.eliminateIfThenElse(compound);

    System.out.println(result);
  }
}
