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
public class EquivalenceRemoverTest {

  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);
  Expression e1 = NumericBooleanExpression.create(x, NumericComparator.LT, c1);
  Expression negE1 = Negation.create(e1);
  Expression e2 = NumericBooleanExpression.create(x, NumericComparator.LE, c2);
  Expression negE2 = Negation.create(e2);

  Expression p1 = PropositionalCompound.create(e1, LogicalOperator.AND, e2);
  Expression p2 = NumericBooleanExpression.create(x, NumericComparator.EQ, c2);
  Expression p3 = PropositionalCompound.create(e1, LogicalOperator.EQUIV, e2);
  Expression negP1 = Negation.create(p1);
  Expression negP2 = Negation.create(p2);

  Expression<Boolean> containsEquiv = PropositionalCompound.create(p1, LogicalOperator.EQUIV, p2);
  Expression<Boolean> containsEquiv2 = PropositionalCompound.create(p1, LogicalOperator.AND, p3);

  Expression<Boolean> equivFree = PropositionalCompound.create(
      PropositionalCompound.create(negP1, LogicalOperator.OR, p2),
      LogicalOperator.AND,
      PropositionalCompound.create(p1, LogicalOperator.OR, negP2));

  Expression<Boolean> equivFree2 = PropositionalCompound.create(
      p1,
      LogicalOperator.AND,
      PropositionalCompound.create(
          PropositionalCompound.create(negE1, LogicalOperator.OR, e2),
          LogicalOperator.AND,
          PropositionalCompound.create(e1, LogicalOperator.OR, negE2)));


  @Test
  public void equivalenceRemoverTest() {
    Expression<Boolean> result = NormalizationUtil.eliminateEquivalence(containsEquiv);

    assertEquals(result, equivFree);
  }

  @Test
  public void nestedEquivalenceRemoverTest() {
    Expression<Boolean> result = NormalizationUtil.eliminateEquivalence(containsEquiv2);

    assertEquals(result, equivFree2);
  }
}
