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

import static java.util.Collections.singleton;
import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.ValuationEntry;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.Set;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("simplifiers")
public class ExpressionTailoringUtilTest {
  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Variable<Integer> j = Variable.create(BuiltinTypes.SINT32, "j");
  Variable<Integer> i = Variable.create(BuiltinTypes.SINT32, "i");

  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 10);
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 5);

  Expression<Boolean> assignmentIJ =
      NumericBooleanExpression.create(
          j, NumericComparator.EQ, NumericCompound.create(i, NumericOperator.PLUS, c2));

  Expression<Boolean> constraintI = NumericBooleanExpression.create(i, NumericComparator.LT, c2);
  Expression<Boolean> constraintJ = NumericBooleanExpression.create(j, NumericComparator.LT, c1);

  Expression<Boolean> assignmentXJ = NumericBooleanExpression.create(x, NumericComparator.EQ, j);

  Set<Variable<?>> vars = singleton(x);

  @Test
  public void disjunctClausesTest() {
    // FIXME: test requires semantically invalid statements
    Expression<Boolean> testInput =
        ExpressionUtil.and(constraintJ, (Expression<Boolean>) (Expression) x);
    assertEquals(ExpressionTailoringUtil.tailor(testInput, vars), x);
  }

  @Test
  public void directJoinedTest() {
    Expression<Boolean> testInput = ExpressionUtil.and(assignmentXJ, constraintJ, constraintI);
    Expression<Boolean> expected = ExpressionUtil.and(assignmentXJ, constraintJ);
    assertEquals(ExpressionTailoringUtil.tailor(testInput, vars), expected);
  }

  @Test
  public void chainedWithOverlayTest() {
    Expression<Boolean> testInput =
        ExpressionUtil.and(assignmentIJ, constraintI, constraintJ, assignmentXJ);
    Expression<Boolean> expected =
        ExpressionUtil.and(assignmentXJ, assignmentIJ, constraintI, constraintJ);
    assertEquals(ExpressionTailoringUtil.tailor(testInput, vars), expected);
  }

  @Test
  public void debuggingWhileLoopTest() {
    Variable<Boolean> a = Variable.create(BuiltinTypes.BOOL, "a");
    Variable<Boolean> b = Variable.create(BuiltinTypes.BOOL, "b");
    Variable<Boolean> c = Variable.create(BuiltinTypes.BOOL, "c");
    Expression<Boolean> part1 = ExpressionUtil.and(new Negation(a), new Negation(b));
    Expression<Boolean> part2 = ExpressionUtil.and(c, new Negation(part1));
    Valuation init = new Valuation();
    init.addEntry(new ValuationEntry<>(a, true));
    init.addEntry(new ValuationEntry<>(b, false));
    assertEquals(ExpressionTailoringUtil.tailor(part2, init.getVariables()), new Negation(part1));
  }
}
