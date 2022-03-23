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

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.flattenedExpression.FlatBooleanExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("simplifiers")
public class DuplicationRemoverTest {

  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 3);
  Variable<Integer> x2 = Variable.create(BuiltinTypes.SINT32, "y");
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 4);
  Expression<Boolean> lessThanExpression =
      NumericBooleanExpression.create(x, NumericComparator.LT, c1);
  Expression<Boolean> greaterThan = new NumericBooleanExpression(x2, NumericComparator.LT, c2);
  Expression<Boolean> assignment = new NumericBooleanExpression(x, NumericComparator.EQ, c2);

  @Test
  public void simpleDuplicationTest() {
    Expression<Boolean> longerExpression =
        ExpressionUtil.and(
            lessThanExpression, lessThanExpression, lessThanExpression, lessThanExpression);

    ExpressionUtil.simplify(longerExpression);

    Expression<Boolean> withoutDuplication = ExpressionUtil.simplifyAgressiv(longerExpression);

    assertEquals(withoutDuplication, lessThanExpression);
  }

  @Test
  public void simpleDuplication2Test() {
    Expression<Boolean> longerExpression = ExpressionUtil.and(greaterThan, lessThanExpression);
    longerExpression = ExpressionUtil.or(longerExpression, greaterThan);

    Expression<Boolean> simplified = ExpressionUtil.simplifyAgressiv(longerExpression);
    assertEquals(simplified.toString(), longerExpression.toString());
  }

  @Test
  public void simpleDuplicationOrTest() {
    Expression<Boolean> firstPart = ExpressionUtil.or(assignment, assignment);
    Expression<Boolean> secondPart =
        ExpressionUtil.and(lessThanExpression, greaterThan, lessThanExpression);
    Expression<Boolean> thirdPart =
        ExpressionUtil.and(new Negation(firstPart), new Negation(secondPart));

    Expression<Boolean> expected =
        ExpressionUtil.and(
            new Negation(assignment),
            new Negation(ExpressionUtil.and(lessThanExpression, greaterThan)));

    Expression<Boolean> flat = thirdPart.accept(FlatExpressionVisitor.getInstance(), null);
    assertEquals(flat.getChildren()[0].getClass(), Negation.class);
    assertEquals(
        ((Negation) flat.getChildren()[0]).getNegated().getClass(), FlatBooleanExpression.class);

    Expression<Boolean> first = thirdPart.accept(FlatExpressionVisitor.getInstance(), null);
    Expression<Boolean> second = first.accept(SimplificationVisitor.getInstance(), null);

    assertEquals(second, expected);
  }
}
