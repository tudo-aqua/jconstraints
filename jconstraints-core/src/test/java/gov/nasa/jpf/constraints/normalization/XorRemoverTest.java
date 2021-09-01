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
public class XorRemoverTest {

  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);
  Expression<Boolean> e1 = NumericBooleanExpression.create(x, NumericComparator.EQ, c1);
  Expression<Boolean> e2 = NumericBooleanExpression.create(x, NumericComparator.EQ, c2);

  Expression<Boolean> xorExpression = PropositionalCompound.create(e1, LogicalOperator.XOR, e2);
  Expression<Boolean> first = PropositionalCompound.create(e1, LogicalOperator.OR, e2);
  Expression<Boolean> second = PropositionalCompound.create(Negation.create(e1), LogicalOperator.OR, Negation.create(e2));
  Expression<Boolean> xorFree = PropositionalCompound.create(first, LogicalOperator.AND, second);

  Expression<Boolean> nestedXor = PropositionalCompound.create(e1, LogicalOperator.IMPLY, xorExpression);
  Expression<Boolean> xorFree2 = PropositionalCompound.create(e1, LogicalOperator.IMPLY, xorFree);

  @Test
  public void xorTest() {
    Expression<Boolean> result = NormalizationUtil.eliminateXOR(xorExpression);

    assertEquals(result, xorFree);
  }

  @Test
  public void nestedXorTest() {
    Expression<Boolean> result = NormalizationUtil.eliminateXOR(nestedXor);

    assertEquals(result, xorFree2);
  }
}
