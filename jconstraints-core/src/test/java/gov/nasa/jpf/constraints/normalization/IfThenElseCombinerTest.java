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

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.normalization.experimentalVisitors.IfThenElseCombinerVisitor;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("normalization")
public class IfThenElseCombinerTest {

  Variable<Boolean> b = Variable.create(BuiltinTypes.BOOL, "b");
  Variable<Boolean> b2 = Variable.create(BuiltinTypes.BOOL, "b2");
  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Variable<Integer> y = Variable.create(BuiltinTypes.SINT32, "y");
  Variable<Integer> p = Variable.create(BuiltinTypes.SINT32, "p");
  Variable<Integer> q = Variable.create(BuiltinTypes.SINT32, "q");
  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);
  Expression e1 = NumericBooleanExpression.create(x, NumericComparator.EQ, c1);
  Expression e2 = NumericBooleanExpression.create(x, NumericComparator.EQ, c2);

  @Test
  public void combiningIfThenElseTest1() {
    Expression<Boolean> compound = NumericBooleanExpression.create(
        IfThenElse.create(b, IfThenElse.create(b, x, y), y),
        NumericComparator.EQ,
        NumericCompound.create(
            IfThenElse.create(b2, p, q),
            NumericOperator.PLUS,
            IfThenElse.create(b2, p, q)));

    Expression<Boolean> result = IfThenElseCombinerVisitor.getInstance().apply(compound, null);

    System.out.println(result);
  }

  @Test
  public void combiningIfThenElseTest2() {
    Expression<Boolean> compound = PropositionalCompound.create(
        IfThenElse.create(b, IfThenElse.create(b, e1, e2), e1),
        LogicalOperator.AND,
        NumericBooleanExpression.create(p, NumericComparator.EQ,
        NumericCompound.create(
            IfThenElse.create(b2, p, q),
            NumericOperator.PLUS,
            IfThenElse.create(b2, p, q))));

    Expression<Boolean> result = IfThenElseCombinerVisitor.getInstance().apply(compound, null);

    System.out.println(result);
  }
}
