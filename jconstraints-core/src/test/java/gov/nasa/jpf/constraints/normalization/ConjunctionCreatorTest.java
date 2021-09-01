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
import static org.junit.jupiter.api.Assertions.assertNotEquals;

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
//tests for the NormalizationUtil.createCNF method, which includes the ConjunctionCreatorVisitor
public class ConjunctionCreatorTest {

  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Variable<Integer> y = Variable.create(BuiltinTypes.SINT32, "y");
  Variable<Boolean> b1 = Variable.create(BuiltinTypes.BOOL, "b1");
  Variable<Boolean> b2 = Variable.create(BuiltinTypes.BOOL, "b2");

  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);

  Expression e1 = NumericBooleanExpression.create(x, NumericComparator.LT, c1);
  Expression e2 = NumericBooleanExpression.create(y, NumericComparator.LE, c2);
  Expression e3 = NumericBooleanExpression.create(x, NumericComparator.GE, c1);
  Expression e4 = NumericBooleanExpression.create(y, NumericComparator.EQ, c2);

  Expression con1 = PropositionalCompound.create(e3, LogicalOperator.AND, e4);
  Expression dis1 = PropositionalCompound.create(e3, LogicalOperator.OR, e4);
  Expression con2 = PropositionalCompound.create(e1, LogicalOperator.AND, e2);
  Expression dis2 = PropositionalCompound.create(e1, LogicalOperator.OR, e2);
  Expression dis3 = PropositionalCompound.create(e1, LogicalOperator.OR, con2);

  Expression disjunction = PropositionalCompound.create(PropositionalCompound.create(e3, LogicalOperator.AND, e4), LogicalOperator.OR, b1);
  Expression expected = PropositionalCompound.create(PropositionalCompound.create(e3, LogicalOperator.OR, b1), LogicalOperator.AND, PropositionalCompound.create(e4, LogicalOperator.OR, b1));
  Expression nestedDisjunction = PropositionalCompound.create(e3, LogicalOperator.OR, disjunction);

  @Test
  //case: (A AND B)
  public void basicTest1(){
    Expression simpleConjunction = PropositionalCompound.create(e3, LogicalOperator.AND, e4);

    Expression<Boolean> cnf = NormalizationUtil.createCNF(simpleConjunction);

    assertEquals(cnf, simpleConjunction);
  }

  @Test
  //case: (A OR B)
  public void basicTest2(){
    Expression simpleDisjunction = PropositionalCompound.create(e3, LogicalOperator.OR, e4);

    Expression<Boolean> cnf = NormalizationUtil.createCNF(simpleDisjunction);

    assertEquals(cnf, simpleDisjunction);
  }

  @Test
  //case: (A AND B) OR C
  public void disjunctionTest(){
    Expression<Boolean> cnf = NormalizationUtil.createCNF(disjunction);

    assertEquals(cnf, expected);
  }

  @Test
  //case: (A OR B) OR C
  public void disjunctionTest2(){
    Expression disjunction2 = PropositionalCompound.create(PropositionalCompound.create(e3, LogicalOperator.OR, e4), LogicalOperator.OR, b1);

    Expression<Boolean> cnf = NormalizationUtil.createCNF(disjunction2);

    assertEquals(cnf, disjunction2);
  }

  @Test
  //case: A AND (A OR B)
  public void conjunctionTest1(){
    Expression conjunction1 = PropositionalCompound.create(b1, LogicalOperator.AND, PropositionalCompound.create(b1, LogicalOperator.OR, b2));

    Expression<Boolean> cnf = NormalizationUtil.createCNF(conjunction1);

    assertEquals(cnf, conjunction1);
  }

  @Test
  //case: (A) OR (C AND D)
  public void disjunctionTest3(){
    Expression disjunction3 = PropositionalCompound.create(b1, LogicalOperator.OR, PropositionalCompound.create(e3, LogicalOperator.AND, e4));
    Expression expected3 = PropositionalCompound.create(PropositionalCompound.create(b1, LogicalOperator.OR, e3), LogicalOperator.AND, PropositionalCompound.create(b1, LogicalOperator.OR, e4));

    Expression<Boolean> cnf = NormalizationUtil.createCNF(disjunction3);

    assertEquals(cnf, expected3);
  }

  @Test
  //case: (A) OR (C OR D)
  public void disjunctionTest4(){
    Expression disjunction4 = PropositionalCompound.create(b1, LogicalOperator.OR, PropositionalCompound.create(e3, LogicalOperator.OR, e4));

    Expression<Boolean> cnf = NormalizationUtil.createCNF(disjunction4);

    assertEquals(cnf, disjunction4);
  }

  @Test
  //case: (A AND B) OR (C AND D)
  public void disjunctionTest5(){
    Expression disjunction5 = PropositionalCompound.create(con1, LogicalOperator.OR, con2);
    Expression expected = PropositionalCompound.create(
        PropositionalCompound.create(
            PropositionalCompound.create(e3, LogicalOperator.OR, e1),
            LogicalOperator.AND,
            PropositionalCompound.create(e3, LogicalOperator.OR, e2)),
        LogicalOperator.AND,
            PropositionalCompound.create(
                PropositionalCompound.create(e4, LogicalOperator.OR, e1),
                LogicalOperator.AND,
                PropositionalCompound.create(e4, LogicalOperator.OR, e2))
    );

    Expression<Boolean> cnf = NormalizationUtil.createCNF(disjunction5);
    assertEquals(cnf, expected);
  }

  @Test
  //case: (A OR B) OR (C OR D)
  public void disjunctionTest6(){
    Expression disjunction6 = PropositionalCompound.create(dis1, LogicalOperator.OR, dis2);

    Expression<Boolean> cnf = NormalizationUtil.createCNF(disjunction6);

    assertEquals(cnf, disjunction6);
  }

  @Test
  //case: (A OR B) OR (C OR (D AND E))
  public void disjunctionNestedTest(){
    Expression disjunction6 = PropositionalCompound.create(dis1, LogicalOperator.OR, dis3);

    Expression<Boolean> cnf = NormalizationUtil.createCNF(disjunction6);

    System.out.print(cnf);
  }

  @Test
  //case: (A AND B) OR (C OR D)
  public void disjunctionTest7(){
    Expression disjunction7 = PropositionalCompound.create(con1, LogicalOperator.OR, dis1);
    Expression expected = PropositionalCompound.create(
        PropositionalCompound.create(e3, LogicalOperator.OR, e4),
        LogicalOperator.AND,
        PropositionalCompound.create(e4, LogicalOperator.OR, e3));

    Expression<Boolean> cnf = NormalizationUtil.createCNF(disjunction7);

    assertEquals(cnf, expected);
  }

  @Test
  //case: (A OR B) OR (C AND D)
  public void disjunctionTest8(){
    Expression disjunction8 = PropositionalCompound.create(dis1, LogicalOperator.OR, con1);
    Expression expected = PropositionalCompound.create(
        PropositionalCompound.create(e3, LogicalOperator.OR, e4),
        LogicalOperator.AND,
        PropositionalCompound.create(e3, LogicalOperator.OR, e4));

    Expression<Boolean> cnf = NormalizationUtil.createCNF(disjunction8);

    assertEquals(cnf, expected);
  }

  @Test
  //A OR ((A AND B) OR C)
  public void nestedDisjunctionTest(){
    Expression<Boolean> cnf = NormalizationUtil.createCNF(nestedDisjunction);
    Expression nestedExpected = PropositionalCompound.create(
        PropositionalCompound.create(e3, LogicalOperator.OR, b1),
        LogicalOperator.AND,
        ExpressionUtil.or(e3,e4, b1));

    assertEquals(cnf, nestedExpected);
  }

  //actually not needed as quantifiers have to be removed before transformation
  @Test
  public void quantifierTest(){
    List<Variable<?>> bound = new ArrayList<>();
    bound.add(x);
    bound.add(y);
    Expression quantifiedDisjunction = QuantifierExpression.create(Quantifier.FORALL, bound, disjunction);
    Expression<Boolean> cnf = NormalizationUtil.createCNF(quantifiedDisjunction);

    System.out.println(quantifiedDisjunction);
    System.out.println(cnf);
  }

  @Test
  public void andTest(){
    Expression and = PropositionalCompound.create(
        PropositionalCompound.create(b1, LogicalOperator.OR, b2),
        LogicalOperator.AND,
        PropositionalCompound.create(
            PropositionalCompound.create(b1, LogicalOperator.OR, b2),
            LogicalOperator.AND,
            PropositionalCompound.create(b1, LogicalOperator.AND, b2)));

    Expression<Boolean> cnf = NormalizationUtil.createCNF(and);

    assertEquals(cnf, and);
  }

  @Test
  public void nestedTest1(){
    Expression nested = PropositionalCompound.create(
        PropositionalCompound.create(e3, LogicalOperator.AND, e4),
        LogicalOperator.OR,
        PropositionalCompound.create(e3, LogicalOperator.OR, PropositionalCompound.create(e3, LogicalOperator.AND, e4)));

    Expression<Boolean> cnf = NormalizationUtil.createCNF(nested);

    Expression expected = PropositionalCompound.create(
        PropositionalCompound.create(e3, LogicalOperator.AND, PropositionalCompound.create(e3, LogicalOperator.OR, e4)),
        LogicalOperator.AND,
        PropositionalCompound.create(
            PropositionalCompound.create(e4, LogicalOperator.OR, e3),
            LogicalOperator.AND,
            PropositionalCompound.create(e4, LogicalOperator.OR, e3)));

    assertEquals(cnf, expected);
  }

  @Test
  public void nestedTest2(){
    Expression nested2 = PropositionalCompound.create(
        PropositionalCompound.create(b1, LogicalOperator.AND, b2),
        LogicalOperator.OR,
        PropositionalCompound.create(b1, LogicalOperator.AND, PropositionalCompound.create(b1, LogicalOperator.OR, b2)));

    Expression expected = ExpressionUtil.and(ExpressionUtil.and(b1, ExpressionUtil.or(b1, b2)),
        ExpressionUtil.and(ExpressionUtil.or(b2, b1), ExpressionUtil.or(b2, b1)));

    Expression<Boolean> simpleCnf = (Expression<Boolean>) nested2.accept(ConjunctionCreatorVisitor.getInstance(), null);
    Expression<Boolean> cnf = NormalizationUtil.createCNF(nested2);

    System.out.println(nested2);
    System.out.println(simpleCnf);
    System.out.println(cnf);
    assertEquals(cnf, expected);
  }

  @Test
  public void nestedTest3(){
    Expression nested3 = ExpressionUtil.and(b1, ExpressionUtil.and(ExpressionUtil.or(ExpressionUtil.and(e3,e3)),e3),
        ExpressionUtil.or(e4, ExpressionUtil.and(e4, e4)));

    Expression<Boolean> simpleCnf = (Expression<Boolean>) nested3.accept(ConjunctionCreatorVisitor.getInstance(), null);
    Expression<Boolean> cnf = NormalizationUtil.createCNF(nested3);
    System.out.println(nested3);
    System.out.println(simpleCnf);
    System.out.println(cnf);
    assertNotEquals(cnf, nested3);
  }

  @Test
  public void nestedTest4(){
    Expression nested4 = ExpressionUtil.or(ExpressionUtil.or(b1, b2), ExpressionUtil.or(ExpressionUtil.and(e3, e4)), ExpressionUtil.or(e3, e4));

    Expression<Boolean> simpleCnf = (Expression<Boolean>) nested4.accept(ConjunctionCreatorVisitor.getInstance(), null);
    Expression<Boolean> cnf = NormalizationUtil.createCNF(nested4);

    System.out.println(simpleCnf);
    System.out.println(cnf);

    assertNotEquals(cnf, nested4);
  }

  @Test
  public void nestedTest5(){
    Expression nested = PropositionalCompound.create(
        PropositionalCompound.create(b1, LogicalOperator.AND, b2),
        LogicalOperator.OR,
        PropositionalCompound.create(
            PropositionalCompound.create(b1, LogicalOperator.AND, b2),
            LogicalOperator.OR,
            PropositionalCompound.create(b1, LogicalOperator.AND, b2)));
    Expression<Boolean> simpleCnf = (Expression<Boolean>) nested.accept(ConjunctionCreatorVisitor.getInstance(), null);
    Expression<Boolean> cnf = NormalizationUtil.createCNF(nested);

    System.out.println(nested);
    System.out.println(simpleCnf);
    System.out.println(cnf);
  }

  @Test
  public void nestedTest6(){
    Expression nested = ExpressionUtil.or(ExpressionUtil.and(e1, e1, e1), ExpressionUtil.and(e2, e2, e2));

    Expression expected = ExpressionUtil.or(e1, e2);
    Expression<Boolean> simpleCnf = (Expression<Boolean>) nested.accept(ConjunctionCreatorVisitor.getInstance(), null);
    Expression<Boolean> cnf = NormalizationUtil.createCNF(nested);

    System.out.println(nested);
    System.out.println(simpleCnf);
    System.out.println(cnf);

    assertEquals(cnf, expected);
  }
}


