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
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("normalization")
public class SkolemizationTest {

  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Variable<Integer> y = Variable.create(BuiltinTypes.SINT32, "y");
  Variable<Integer> z = Variable.create(BuiltinTypes.SINT32, "z");

  Variable<Boolean> b1 = Variable.create(BuiltinTypes.BOOL, "b1");
  Variable<Boolean> b2 = Variable.create(BuiltinTypes.BOOL, "b2");

  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);

  Expression<Boolean> e1 = NumericBooleanExpression.create(x, NumericComparator.LT, c1);
  Expression<Boolean> e2 = NumericBooleanExpression.create(y, NumericComparator.LE, c2);
  Expression<Boolean> e4 = NumericBooleanExpression.create(y, NumericComparator.EQ, c2);
  Expression<Boolean> e5 = NumericBooleanExpression.create(x, NumericComparator.GE, y);
  Expression<Boolean> e6 = PropositionalCompound.create(b1, LogicalOperator.OR, e1);
  Expression<Boolean> e8 = NumericBooleanExpression.create(z, NumericComparator.EQ, c2);
  Expression<Boolean> con1 = PropositionalCompound.create(e1, LogicalOperator.AND, e4);

  @Test
  // only forall
  public void forallTest() {
    List<Variable<?>> bound = new ArrayList<>();
    bound.add(x);
    Expression<Boolean> quantified = QuantifierExpression.create(Quantifier.FORALL, bound, con1);

    Expression<Boolean> skolemized = NormalizationUtil.skolemize(quantified);

    System.out.println(quantified);
    System.out.println(skolemized);
  }

  @Test
  public void forallTest2() {
    List<Variable<?>> bound = new ArrayList<>();
    bound.add(x);
    Expression<Boolean> quantified =
        ExpressionUtil.or(e8, QuantifierExpression.create(Quantifier.FORALL, bound, con1));

    Expression<Boolean> skolemized = NormalizationUtil.skolemize(quantified);

    System.out.println(quantified);
    System.out.println(skolemized);
  }

  @Test
  // only outer exists, no forall
  public void outerExistsTest1() {
    List<Variable<?>> bound1 = new ArrayList<Variable<?>>();
    bound1.add(x);
    Expression<Boolean> quantified = QuantifierExpression.create(Quantifier.EXISTS, bound1, e1);
    Expression<Boolean> skolemized = NormalizationUtil.skolemize(quantified);

    System.out.println(skolemized);
  }

  @Test
  // only outer exists, inner forall
  public void outerExistsTest2() {
    List<Variable<?>> bound1 = new ArrayList<Variable<?>>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<Variable<?>>();
    bound2.add(y);
    Expression<Boolean> quantified =
        QuantifierExpression.create(
            Quantifier.EXISTS,
            bound1,
            QuantifierExpression.create(Quantifier.FORALL, bound2, con1));
    Expression<Boolean> skolemized = NormalizationUtil.skolemize(quantified);

    System.out.println(skolemized);
  }

  @Test
  // inner exists
  public void innerExistsTest() {
    List<Variable<?>> bound1 = new ArrayList<Variable<?>>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<Variable<?>>();
    bound2.add(y);
    Expression<Boolean> quantified =
        QuantifierExpression.create(
            Quantifier.FORALL, bound1, QuantifierExpression.create(Quantifier.EXISTS, bound2, e5));

    Expression<Boolean> renamed = NormalizationUtil.renameAllBoundVars(quantified);
    Expression<Boolean> mini = NormalizationUtil.miniScope(renamed);
    Expression<Boolean> skolemized = NormalizationUtil.skolemize(mini);
    System.out.println(quantified);
    System.out.println(renamed);
    System.out.println(mini);
    System.out.println(skolemized);
  }

  @Test
  // multiple exists
  public void multiplePathsTest1() {
    List<Variable<?>> bound1 = new ArrayList<>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<>();
    bound2.add(y);
    List<Variable<?>> bound3 = new ArrayList<>();
    bound3.add(z);

    Expression<Boolean> quantified =
        QuantifierExpression.create(
            Quantifier.FORALL,
            bound1,
            ExpressionUtil.and(
                QuantifierExpression.create(Quantifier.FORALL, bound2, e2),
                QuantifierExpression.create(Quantifier.EXISTS, bound3, e8)));
    Expression<Boolean> skolemized = NormalizationUtil.skolemize(quantified);

    System.out.println(quantified);
    System.out.println(skolemized);
  }

  @Test
  // multiple exists
  public void multiplePathsTest2() {
    List<Variable<?>> bound1 = new ArrayList<>();
    bound1.add(x);
    List<Variable<?>> bound3 = new ArrayList<>();
    bound3.add(z);

    Expression<Boolean> quantified =
        ExpressionUtil.and(
            QuantifierExpression.create(Quantifier.FORALL, bound1, e1),
            QuantifierExpression.create(Quantifier.EXISTS, bound3, e8));
    Expression<Boolean> skolemized = NormalizationUtil.skolemize(quantified);

    System.out.println(quantified);
    System.out.println(skolemized);
  }

  @Test
  // multiple exists
  public void multipleExistsTest() {
    List<Variable<?>> bound1 = new ArrayList<>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<>();
    bound2.add(y);
    List<Variable<?>> bound3 = new ArrayList<>();
    bound3.add(b1);
    List<Variable<?>> bound4 = new ArrayList<>();
    bound4.add(b2);

    Expression<Boolean> quantified =
        ExpressionUtil.and(
            QuantifierExpression.create(
                Quantifier.FORALL,
                bound1,
                ExpressionUtil.and(
                    QuantifierExpression.create(Quantifier.FORALL, bound2, e2),
                    QuantifierExpression.create(Quantifier.EXISTS, bound3, e6))),
            QuantifierExpression.create(
                Quantifier.EXISTS,
                bound4,
                ExpressionUtil.and(
                    QuantifierExpression.create(Quantifier.FORALL, bound1, e8), b2)));
    Expression<Boolean> mini = NormalizationUtil.miniScope(quantified);
    Expression<Boolean> skolemized = NormalizationUtil.skolemize(mini);

    System.out.println(quantified);
    System.out.println(mini);
    System.out.println(skolemized);
  }

  @Test
  public void nameClashTest() {
    Collection<Variable<?>> test = new ArrayList<>();
    List<Variable<?>> bound1 = new ArrayList<>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<>();
    bound2.add(y);
    Variable<Integer> modVar = Variable.create(BuiltinTypes.SINT32, "y");
    Expression<Boolean> e7 = NumericBooleanExpression.create(c1, NumericComparator.EQ, modVar);

    Expression<Boolean> quantified =
        ExpressionUtil.and(
            QuantifierExpression.create(
                Quantifier.EXISTS,
                bound1,
                ExpressionUtil.and(
                    e7, QuantifierExpression.create(Quantifier.FORALL, bound2, e2))));
    Expression<Boolean> renamed = NormalizationUtil.renameAllBoundVars(quantified);
    Expression<Boolean> skolemized = NormalizationUtil.skolemize(renamed);

    quantified.collectFreeVariables(test);
    System.out.println(NormalizationUtil.containsDuplicateNames(test));
    System.out.println(test);
    System.out.println(quantified);
    System.out.println(renamed);
    System.out.println(skolemized);
  }
}
