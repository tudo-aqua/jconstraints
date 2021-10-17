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
public class MiniScopingTest {

  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Variable<Integer> y = Variable.create(BuiltinTypes.SINT32, "y");

  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);

  Expression<Boolean> e1 = NumericBooleanExpression.create(x, NumericComparator.LT, c1);
  Expression<Boolean> e2 = NumericBooleanExpression.create(y, NumericComparator.LE, c2);
  Expression<Boolean> e3 = NumericBooleanExpression.create(x, NumericComparator.GE, c1);
  Expression<Boolean> e4 = NumericBooleanExpression.create(y, NumericComparator.EQ, c2);

  Expression<Boolean> con1 = PropositionalCompound.create(e3, LogicalOperator.AND, e4);
  Expression<Boolean> dis1 = PropositionalCompound.create(e2, LogicalOperator.OR, e4);

  @Test
  //free vars left
  public void leftTest(){
    List<Variable<?>> bound = new ArrayList<>();
    bound.add(x);
    Expression<Boolean> q = ExpressionUtil.or(e1,
            QuantifierExpression.create(Quantifier.FORALL, bound, ExpressionUtil.or(e2, e1)));

    Expression<Boolean> minimized = NormalizationUtil.miniScope(q);
    System.out.println(minimized);
  }

  @Test
  //free vars right
  public void rightTest(){
    List<Variable<?>> bound = new ArrayList<>();
    bound.add(x);
    Expression<Boolean> q = ExpressionUtil.or(QuantifierExpression.create(Quantifier.FORALL, bound, ExpressionUtil.and(e1, e2)), dis1);

    Expression<Boolean> minimized = NormalizationUtil.miniScope(q);
    System.out.println(minimized);
  }

  @Test
  //free vars in both
  public void existsTest(){
    List<Variable<?>> bound = new ArrayList<>();
    bound.add(x);
    Expression<Boolean> q = QuantifierExpression.create(Quantifier.EXISTS, bound, ExpressionUtil.and(ExpressionUtil.or(e1, e2), con1));

    Expression<Boolean> minimized = NormalizationUtil.miniScope(q);
    System.out.println(q);
    System.out.println(minimized);
  }

  @Test
  //free vars in both
  public void forallTest(){
    List<Variable<?>> bound = new ArrayList<>();
    bound.add(x);
    Expression<Boolean> q = QuantifierExpression.create(Quantifier.FORALL, bound, ExpressionUtil.or(ExpressionUtil.and(e1, e2), con1));

    Expression<Boolean> minimized = NormalizationUtil.miniScope(q);
    System.out.println(q);
    System.out.println(minimized);
  }

  @Test
  //free vars in both
  public void multipleQuantifierTest(){
    List<Variable<?>> bound1 = new ArrayList<>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<>();
    bound2.add(y);
    Expression<Boolean> q = QuantifierExpression.create(Quantifier.EXISTS, bound1,
        QuantifierExpression.create(Quantifier.FORALL, bound2, ExpressionUtil.and(ExpressionUtil.or(e1, e2), con1)));

    Expression<Boolean> minimized = NormalizationUtil.miniScope(q);
    System.out.println(q);
    System.out.println(minimized);
  }

  @Test
  //free vars in both
  public void notMixedQuantifierTest1(){
    List<Variable<?>> bound1 = new ArrayList<>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<>();
    bound2.add(y);
    Expression<Boolean> q = QuantifierExpression.create(Quantifier.FORALL, bound1, ExpressionUtil.and(e1, QuantifierExpression.create(Quantifier.FORALL, bound2, ExpressionUtil.and(e1, e2))));

    Expression<Boolean> minimized = NormalizationUtil.miniScope(q);
    System.out.println(q);
    System.out.println(minimized);
  }

  @Test
  //mixed quantifiers are not allowed to change their order
  public void mixedQuantifierTest1(){
    List<Variable<?>> bound1 = new ArrayList<>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<>();
    bound2.add(y);
    Expression q = QuantifierExpression.create(Quantifier.FORALL, bound1, PropositionalCompound.create(e1, LogicalOperator.AND, QuantifierExpression.create(Quantifier.EXISTS, bound2, PropositionalCompound.create(e1, LogicalOperator.AND, e2))));

    Expression<Boolean> minimized = NormalizationUtil.miniScope(q);
    System.out.println(q);
    System.out.println(minimized);
  }
}


