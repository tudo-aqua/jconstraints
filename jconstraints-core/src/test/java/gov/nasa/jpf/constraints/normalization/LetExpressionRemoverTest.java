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
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("normalization")
public class LetExpressionRemoverTest {

  Variable<Integer> x1 = Variable.create(BuiltinTypes.SINT32, "x1");
  Variable<Integer> x2 = Variable.create(BuiltinTypes.SINT32, "x2");
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);
  Constant<Integer> c4 = Constant.create(BuiltinTypes.SINT32, 4);
  NumericBooleanExpression partA = NumericBooleanExpression.create(x1, NumericComparator.LE, c4);
  NumericBooleanExpression partB = NumericBooleanExpression.create(x2, NumericComparator.GE, c2);
  NumericCompound<Integer> replacementA = NumericCompound.create(x2, NumericOperator.PLUS, c2);
  NumericCompound<Integer> replacementB = NumericCompound.create(x2, NumericOperator.MINUS, c2);

  Expression<Boolean> letExpression = LetExpression.create(x1, replacementA, partA);
  Expression<Boolean> letFree =
      NumericBooleanExpression.create(replacementA, NumericComparator.LE, c4);
  Expression<Boolean> nestedLet =
      PropositionalCompound.create(
          LetExpression.create(x2, replacementB, partB), LogicalOperator.AND, letExpression);
  Expression<Boolean> letFree2 =
      PropositionalCompound.create(
          NumericBooleanExpression.create(replacementB, NumericComparator.GE, c2),
          LogicalOperator.AND,
          letFree);

  @Test
  public void letTest() {
    Expression<Boolean> result = NormalizationUtil.eliminateLetExpressions(letExpression);

    assertEquals(result, letFree);
  }

  @Test
  public void nestedLetTest() {
    Expression<Boolean> result = NormalizationUtil.eliminateLetExpressions(nestedLet);

    assertEquals(result, letFree2);
  }

  @Test
  public void quantifiedLetTest() {
    List<Variable<?>> bound = new ArrayList();
    bound.add(x1);
    Expression<Boolean> quantified =
        QuantifierExpression.create(Quantifier.EXISTS, bound, letExpression);
    Expression<Boolean> result = NormalizationUtil.eliminateLetExpressions(quantified);

    System.out.println(result);
  }

  @Test
  public void innerLetTest() {
    Expression<Boolean> multipleLets = ExpressionUtil.or(nestedLet, letExpression);
    Expression<Boolean> result = NormalizationUtil.eliminateLetExpressions(multipleLets);

    System.out.println(result);
  }
}
