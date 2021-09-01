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
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.*;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

@Tag("normalization")
public class NormalizationUtilTest {

  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Variable<Integer> y = Variable.create(BuiltinTypes.SINT32, "y");
  Variable<Boolean> b = Variable.create(BuiltinTypes.BOOL, "b");
  Variable<Boolean> b1 = Variable.create(BuiltinTypes.BOOL, "b1");
  Variable<Boolean> b2 = Variable.create(BuiltinTypes.BOOL, "b2");
  Variable<Integer> p = Variable.create(BuiltinTypes.SINT32, "p");
  Variable<Integer> q = Variable.create(BuiltinTypes.SINT32, "q");

  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 1);
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 2);

  Expression<Boolean> e1 = NumericBooleanExpression.create(x, NumericComparator.LT, c1);
  Expression<Boolean> e2 = NumericBooleanExpression.create(y, NumericComparator.LE, c2);
  Expression<Boolean> e3 = NumericBooleanExpression.create(p, NumericComparator.EQ, c2);
  Expression<Boolean> e4 = NumericBooleanExpression.create(y, NumericComparator.EQ, c2);
  Expression<Boolean> e5 = NumericBooleanExpression.create(x, NumericComparator.GE, y);

  Expression<Boolean> con1 = PropositionalCompound.create(e1, LogicalOperator.AND, e2);
  Expression<Boolean> dis1 = PropositionalCompound.create(e1, LogicalOperator.OR, e2);
  Expression<Boolean> xor2 = PropositionalCompound.create(e1, LogicalOperator.XOR, e2);
  Expression<Boolean> xor1 = PropositionalCompound.create(xor2, LogicalOperator.XOR, e2);
  Expression<Boolean> imply = PropositionalCompound.create(con1, LogicalOperator.IMPLY, e2);
  Expression<Boolean> negation1 = Negation.create(xor1);
  Expression<Boolean> negation2 = Negation.create(imply);
  Expression<Boolean> con2 = ExpressionUtil.and(e1, e2, e1);
  Expression<Boolean> con3 = PropositionalCompound.create(e1, LogicalOperator.AND, e1);
  Expression<Boolean> negE3 = NumericBooleanExpression.create(x, NumericComparator.LT, c1);

  @Test
  public void quantifierCounterTest(){
    List<Variable<?>> bound1 = new ArrayList<>();
    bound1.add(x);
    List<Variable<?>> bound3 = new ArrayList<>();
    bound3.add(y);
    Expression quantified = ExpressionUtil.and(
        QuantifierExpression.create(Quantifier.FORALL, bound1, e1),
        QuantifierExpression.create(Quantifier.EXISTS, bound3, e2));
    int count = NormalizationUtil.countQuantifiers(quantified);

    assertEquals(count, 2);
  }

  @Test
  public void iteCountTest(){
    Expression<Boolean> compound = NumericBooleanExpression.create(
        IfThenElse.create(b, IfThenElse.create(b, x, y), y),
        NumericComparator.EQ,
        NumericCompound.create(
            IfThenElse.create(b2, p, q),
            NumericOperator.PLUS,
            IfThenElse.create(b2, p, q)));

    int count = NormalizationUtil.countItes(compound);

    assertEquals(count, 4);
  }

  @Test
  public void iteDepthTest(){
    Expression<Boolean> compound = NumericBooleanExpression.create(
        IfThenElse.create(b, IfThenElse.create(b, x, y), y),
        NumericComparator.EQ,
        NumericCompound.create(
            IfThenElse.create(b2, p, q),
            NumericOperator.PLUS,
            IfThenElse.create(b2, p, q)));

    int count = NormalizationUtil.maxIteDepth(compound);

    assertEquals(count, 2);
  }

  @Test
  public void iteDepthTest2() {
    Expression<Boolean> compound = NumericBooleanExpression.create(
        IfThenElse.create(b, x, y),
        NumericComparator.EQ,
        NumericCompound.create(
            UnaryMinus.create(c1),
            NumericOperator.PLUS,
            IfThenElse.create(b2, p, q)));

    int count = NormalizationUtil.maxIteDepth(compound);

    assertEquals(count, 1);
  }

  @Test
  public void iteDepthTest3() {
    Expression<Boolean> compound = ExpressionUtil.and(NumericBooleanExpression.create(
        IfThenElse.create(b, x, y),
        NumericComparator.EQ,
        IfThenElse.create(b, IfThenElse.create(b2, IfThenElse.create(b, y, x), q), y)));

    int count = NormalizationUtil.maxIteDepth(compound);

    assertEquals(count, 3);
  }

  @Test
  public void iteCheckTest(){
    Expression<Boolean> compound = NumericBooleanExpression.create(
        NumericCompound.create(IfThenElse.create(b, x, y),NumericOperator.PLUS, y),
        NumericComparator.EQ,
        NumericCompound.create(
            IfThenElse.create(b2, p, q),
            NumericOperator.PLUS,
            IfThenElse.create(b2, p, q)));

    boolean ite = NormalizationUtil.ifThenElseCheck(compound);

    assertTrue(ite);
  }

  @Test
  public void equivalenceCountTest(){
    Expression<Boolean> p1 = PropositionalCompound.create(e1, LogicalOperator.AND, e2);
    Expression<Boolean> p3 = PropositionalCompound.create(e1, LogicalOperator.EQUIV, e2);

    Expression<Boolean> containsEquiv = PropositionalCompound.create(p1, LogicalOperator.EQUIV, p3);

    int count = NormalizationUtil.countEquivalences(containsEquiv);

    assertEquals(count, 2);
  }

  @Test
  public void conjunctionCountTest(){
    Expression<Boolean> con1 = PropositionalCompound.create(e3, LogicalOperator.AND, e1);
    Expression<Boolean> con2 = PropositionalCompound.create(e1, LogicalOperator.AND, e2);
    Expression<Boolean> conjunction = PropositionalCompound.create(con1, LogicalOperator.AND, con2);

    int count = NormalizationUtil.countConjunctions(conjunction);

    assertEquals(count, 3);
  }

  @Test
  public void disjunctionCountTest(){
    Expression<Boolean> con1 = PropositionalCompound.create(e3, LogicalOperator.AND, e1);
    Expression<Boolean> dis2 = PropositionalCompound.create(e1, LogicalOperator.OR, e2);
    Expression<Boolean> disjunction = PropositionalCompound.create(con1, LogicalOperator.OR, dis2);

    int count = NormalizationUtil.countDisjunctions(disjunction);

    assertEquals(count, 2);
  }

  @Test
  public void negationCountTest(){
    Expression<Boolean> disjunction = Negation.create(PropositionalCompound.create(negation1, LogicalOperator.OR, negation2));

    int count = NormalizationUtil.countNegations(disjunction);

    assertEquals(count, 3);
  }

  @Test
  public void xorCountTest(){
    int count = NormalizationUtil.countXORs(xor1);

    assertEquals(count, 2);
  }

  @Test
  public void mixedQuantifiersTest(){
    List<Variable<?>> bound1 = new ArrayList<>();
    bound1.add(x);
    List<Variable<?>> bound3 = new ArrayList<>();
    bound3.add(y);
    Expression<Boolean> quantified = ExpressionUtil.and(
        QuantifierExpression.create(Quantifier.FORALL, bound1, e1),
        QuantifierExpression.create(Quantifier.EXISTS, bound3, e2));
    boolean mixed = NormalizationUtil.mixedQuantifierCheck(quantified);

    assertTrue(mixed);
  }

  @Test
  public void existsTest1(){
    List<Variable<?>> bound1 = new ArrayList<Variable<?>>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<Variable<?>>();
    bound2.add(y);
    Expression<Boolean> quantified = QuantifierExpression.create(Quantifier.FORALL, bound1,
        QuantifierExpression.create(Quantifier.EXISTS, bound2, e5));

    assertTrue(NormalizationUtil.checkForExists(quantified));
  }

  @Test
  public void existsTest2(){
    List<Variable<?>> bound1 = new ArrayList<Variable<?>>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<Variable<?>>();
    bound2.add(y);
    Expression<Boolean> quantified = ExpressionUtil.or(QuantifierExpression.create(Quantifier.FORALL, bound1, e1),
        ExpressionUtil.or(QuantifierExpression.create(Quantifier.FORALL, bound1, e1),
            QuantifierExpression.create(Quantifier.EXISTS, bound2, e5)));

    assertTrue(NormalizationUtil.checkForExists(quantified));
  }

  @Test
  public void existsTest3(){
    List<Variable<?>> bound1 = new ArrayList<Variable<?>>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<Variable<?>>();
    bound2.add(y);
    Expression<Boolean> quantified = ExpressionUtil.or(ExpressionUtil.and(
        QuantifierExpression.create(Quantifier.FORALL, bound1, e1),
        e2,
        QuantifierExpression.create(Quantifier.EXISTS, bound2, e5)));

    assertTrue(NormalizationUtil.checkForExists(quantified));
  }

  @Test
  public void existsInForallTest1(){
    List<Variable<?>> bound1 = new ArrayList<Variable<?>>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<Variable<?>>();
    bound2.add(y);
    Expression<Boolean> quantified = QuantifierExpression.create(Quantifier.FORALL, bound1,
        QuantifierExpression.create(Quantifier.EXISTS, bound2, e5));

    assertTrue(NormalizationUtil.existsInForall(quantified));
  }

  @Test
  public void existsInForallTest2(){
    List<Variable<?>> bound1 = new ArrayList<Variable<?>>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<Variable<?>>();
    bound2.add(y);
    Expression<Boolean> quantified = ExpressionUtil.or(QuantifierExpression.create(Quantifier.FORALL, bound1, e1),
        QuantifierExpression.create(Quantifier.EXISTS, bound2, e5));

    assertFalse(NormalizationUtil.existsInForall(quantified));
  }

  @Test
  public void existsInForallTest3(){
    List<Variable<?>> bound1 = new ArrayList<Variable<?>>();
    bound1.add(x);
    List<Variable<?>> bound2 = new ArrayList<Variable<?>>();
    bound2.add(y);
    Expression<Boolean> quantified = ExpressionUtil.or(QuantifierExpression.create(Quantifier.FORALL, bound1, e1),
        QuantifierExpression.create(Quantifier.EXISTS, bound2, e5),
        QuantifierExpression.create(Quantifier.FORALL, bound1, QuantifierExpression.create(Quantifier.EXISTS, bound2, e5)));

    assertTrue(NormalizationUtil.existsInForall(quantified));
  }

  @Test
  //"clauses" means same operator sequences here (and in the following test methods), not logical clauses
  public void countClausesTest1(){
    Expression<Boolean> expected = PropositionalCompound.create(
        PropositionalCompound.create(e1, LogicalOperator.AND, e2),
        LogicalOperator.OR,
        ExpressionUtil.and(e2, e1, e3));

    assertEquals(NormalizationUtil.countSameOperatorSequences(expected), 2);
  }

  @Test
  public void countClausesTest2(){
    Expression<Boolean> expected = ExpressionUtil.and(e2, e1, e3);

    assertEquals(NormalizationUtil.countSameOperatorSequences(expected), 1);
  }

  @Test
  public void countClausesTest3(){
    Expression<Boolean> expected = ExpressionUtil.or(ExpressionUtil.and(e2, e1, e3),
        ExpressionUtil.and(e2, e4, e3),
        ExpressionUtil.and(e1, e3),
        ExpressionUtil.and(e2, e1));

    assertEquals(NormalizationUtil.countSameOperatorSequences(expected), 4);
  }

  @Test
  public void normalizeTest1(){
    Expression<Boolean> disjunction8 = PropositionalCompound.create(dis1, LogicalOperator.OR, con1);
    Expression<Boolean> cnf = NormalizationUtil.normalize(disjunction8, "cnf");

    System.out.println(disjunction8);
    System.out.println(cnf);
  }

  @Test
  public void normalizeTest2(){
    List<Variable<?>> bound = new ArrayList<>();
    bound.add(x);
    Expression<Boolean> disjunction8 = PropositionalCompound.create(dis1, LogicalOperator.OR, con1);
    Expression<Boolean> quantified = QuantifierExpression.create(Quantifier.FORALL, bound, disjunction8);
    Expression<Boolean> cnf = NormalizationUtil.normalize(quantified, "cnf");

    System.out.println(quantified);
    System.out.println(cnf);
  }

  @Test
  public void normalizeTest3(){
    Expression<Boolean> conjunction7 = PropositionalCompound.create(dis1, LogicalOperator.AND, con1);
    Expression<Boolean> expected = PropositionalCompound.create(
        PropositionalCompound.create(e1, LogicalOperator.AND, e2),
        LogicalOperator.OR,
        PropositionalCompound.create(e2, LogicalOperator.AND, e1));

    Expression<Boolean> dnf = NormalizationUtil.createDNF(conjunction7);

    assertEquals(dnf, expected);
  }

  @Test
  public void normalizeTest4(){
    List<Variable<?>> bound = new ArrayList<>();
    bound.add(x);
    Expression<Boolean> disjunction8 = PropositionalCompound.create(dis1, LogicalOperator.OR, con1);
    Expression<Boolean> quantified = QuantifierExpression.create(Quantifier.FORALL, bound, disjunction8);

    Expression<Boolean> dnf = NormalizationUtil.normalize(quantified, "dnf");

    System.out.println(quantified);
    System.out.println(dnf);
  }

  @Test
  public void checkIfSameOperatorTest1(){
    boolean check = NormalizationUtil.checkIfSameOperator(ExpressionUtil.and(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e2, e3)));

    assertFalse(check);
  }

  @Test
  public void checkIfSameOperatorTest2(){
    boolean check = NormalizationUtil.checkIfSameOperator(ExpressionUtil.and(
        ExpressionUtil.and(e2, e3),
        ExpressionUtil.and(e1, e2, e3)));

    assertTrue(check);
  }

  @Test
  public void collectExpressionsInClauseTest1(){
    LinkedList clauseSet = new LinkedList<>();
    LinkedList<Expression> set = NormalizationUtil.collectExpressionsInSameOperatorSequences(clauseSet, ExpressionUtil.and(
        ExpressionUtil.and(e4, e5),
        ExpressionUtil.and(e1, e2, e3)));

    LinkedList<Expression> expected = new LinkedList<>();
    expected.add(e4);
    expected.add(e5);
    expected.add(e1);
    expected.add(e2);
    expected.add(e3);

    System.out.println(clauseSet);
    System.out.println(expected);
    assertEquals(clauseSet, expected);
  }

  @Test
  public void collectExpressionsInClauseTest2(){
    LinkedList clauseSet = new LinkedList<>();
    LinkedList<Expression> set = NormalizationUtil.collectExpressionsInSameOperatorSequences(clauseSet, ExpressionUtil.and(
        ExpressionUtil.and(e2, e3),
        ExpressionUtil.and(e1, e2, e3)));
    LinkedList<Expression> expected = new LinkedList<>();
    expected.add(e2);
    expected.add(e3);
    expected.add(e1);

    assertEquals(clauseSet, expected);
  }

  @Test
  public void collectExpressionsInClauseTest3(){
    LinkedList clauseSet = new LinkedList<>();
    LinkedList<Expression> set = NormalizationUtil.collectExpressionsInSameOperatorSequences(clauseSet, ExpressionUtil.and(
        ExpressionUtil.and(ExpressionUtil.and(e4, e5), e5),
        ExpressionUtil.and(e1, e2, ExpressionUtil.and(e5, e4, e3))));

    LinkedList<Expression> expected = new LinkedList<>();
    expected.add(e4);
    expected.add(e5);
    expected.add(e1);
    expected.add(e2);
    expected.add(e3);

    assertEquals(clauseSet, expected);
  }

  @Test
  public void checkIfOnlyLiteralsTest1(){
    boolean check = NormalizationUtil.checkIfOnlyLiterals(ExpressionUtil.and(
        ExpressionUtil.and(e2, e3),
        ExpressionUtil.and(e1, e2, e3)));

    assertFalse(check);
  }

  @Test
  public void checkIfOnlyLiteralsTest2(){
    boolean check = NormalizationUtil.checkIfOnlyLiterals(ExpressionUtil.and(b,b1,b2));

    assertTrue(check);
  }

  @Test
  public void duplicatesTest1(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicatesInSameOperatorSequences(con3);
    Expression<Boolean> expected = e1;

    assertEquals(simplified, expected);
  }

  @Test
  public void duplicatesTest2(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicatesInSameOperatorSequences(con2);
    Expression<Boolean> expected = ExpressionUtil.and(e1, e2);

    System.out.println(simplified);
    System.out.println(expected);
    assertEquals(simplified, expected);
  }

  @Test
  public void duplicatesTest3(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicatesInSameOperatorSequences(ExpressionUtil.and(e1, e2, e1, e3, e2));
    Expression<Boolean> expected = ExpressionUtil.and(e1, e2, e3);

    System.out.println(simplified);
    System.out.println(expected);
    assertEquals(simplified, expected);
  }

  @Test
  public void duplicatesTest4(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicatesInSameOperatorSequences(ExpressionUtil.or(e1, e2, e1, e3, e2));
    Expression<Boolean> expected = ExpressionUtil.or(e1, e2, e3);

    System.out.println(simplified);
    System.out.println(expected);
    assertEquals(simplified, expected);
  }

  @Test
  public void duplicatesTest5(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicatesInSameOperatorSequences(ExpressionUtil.or(
        ExpressionUtil.and(e2, e3, e1, e3),
        (ExpressionUtil.or(e1, e2, e1))));

    Expression<Boolean> expected = ExpressionUtil.or(
        ExpressionUtil.and(e2, e3, e1),
        (ExpressionUtil.or(e1, e2)));

    System.out.println(simplified);
    System.out.println(expected);
    assertEquals(simplified, expected);
  }

  @Test
  public void duplicatesTest6(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicatesInSameOperatorSequences(ExpressionUtil.or(
        ExpressionUtil.and(e2, e3, e1, e3),
        (ExpressionUtil.or(e1, e2, e1)),
        ExpressionUtil.and(e3, e2, e3, e2)));

    Expression<Boolean> expected = ExpressionUtil.or(
        ExpressionUtil.and(e2, e3, e1),
        (ExpressionUtil.or(e1, e2)),
        ExpressionUtil.and(e3, e2));

    System.out.println(simplified);
    System.out.println(expected);
    assertEquals(simplified, expected);
  }

  @Test
  public void duplicatesTest7(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicatesInSameOperatorSequences(ExpressionUtil.or(
            ExpressionUtil.and(e2, e3, e1, e3),
            ExpressionUtil.and(e3, e2, e2)));

    Expression<Boolean> expected = ExpressionUtil.or(
            ExpressionUtil.and(e2, e3, e1),
            ExpressionUtil.and(e3, e2));

    System.out.println(simplified);
    System.out.println(expected);
    assertEquals(simplified, expected);
  }

  @Test
  public void duplicatesTest8(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicatesInSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.and(e2, e3, e1, e3),
        ExpressionUtil.or(e2, e3, e1, e1),
        ExpressionUtil.or(e2, e3, e2),
        ExpressionUtil.and(e3, e2, e1, e3)));

    Expression<Boolean> expected = ExpressionUtil.and(
        ExpressionUtil.and(e2, e3, e1),
        ExpressionUtil.or(e2, e3, e1),
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.and(e3, e2, e1));

    System.out.println(simplified);
    System.out.println(expected);
    assertEquals(simplified, expected);
  }

  @Test
  public void duplicatesTest10(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicatesInSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.and(e2, e3, e3, e2),
        ExpressionUtil.and(e2, e3)));

    Expression<Boolean> expected = ExpressionUtil.and(e2, e3);

    System.out.println(simplified);
    System.out.println(expected);
    assertEquals(simplified, expected);
  }

  @Test
  public void duplicatesTest11(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicatesInSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.and(e2, e3),
        ExpressionUtil.and(e1, e2, e3)));

    Expression<Boolean> expected = ExpressionUtil.and(e2, e3, e1);

    System.out.println(simplified);
    System.out.println(expected);
    assertEquals(simplified, expected);
  }

  @Test
  public void duplicatesTest12(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicatesInSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.or(e2, e3, ExpressionUtil.and(e3, e2)),
        ExpressionUtil.or(e2, e3, e2)));

    Expression<Boolean> expected = ExpressionUtil.and(
        ExpressionUtil.or(e2, e3, ExpressionUtil.and(e3, e2)),
        ExpressionUtil.or(e2, e3));

    System.out.println(simplified);
    System.out.println(expected);
    assertEquals(simplified, expected);
  }

  @Test
  public void duplicateClausesTest1(){
    Expression<Boolean> simplified1 = NormalizationUtil.removeDuplicateSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e3)));

    Expression<Boolean> expected = ExpressionUtil.or(e2, e3);

    assertEquals(simplified1, expected);
  }

  @Test
  public void duplicateClausesTest2(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicateSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e2, e3)));

    Expression<Boolean> expected = ExpressionUtil.and(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1));

    assertEquals(simplified, expected);
  }

  @Test
  public void duplicateClausesTest3(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicateSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.and(e2, e3)));

    Expression<Boolean> expected = ExpressionUtil.and(
        ExpressionUtil.and(e2, e3),
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1));

    assertEquals(simplified, expected);
  }

  @Test
  public void duplicateClausesTest4(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicateSameOperatorSequences(ExpressionUtil.or(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e2, e3)));

    Expression<Boolean> expected = ExpressionUtil.or(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        //this part can be removed by NormalizationUtil.removeDuplicates()
        ExpressionUtil.or(e2, e3));

    assertEquals(simplified, expected);
  }

  @Test
  public void duplicateClausesTest7(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicateSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e1, e2)));

    Expression<Boolean> expected = ExpressionUtil.and(
        ExpressionUtil.or(e1, e2),
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1));

    assertEquals(simplified, expected);
  }

  @Test
  public void duplicateClausesTest8(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicateSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e1, e2),
        ExpressionUtil.or(e2, e3)));

    Expression<Boolean> expected = ExpressionUtil.and(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e1, e2),
        ExpressionUtil.or(e2, e1));

    assertEquals(simplified, expected);
  }

  @Test
  public void duplicateClausesTest9(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicateSameOperatorSequences(ExpressionUtil.or(
        ExpressionUtil.and(e2, e1),
        ExpressionUtil.and(e2, e3),
        ExpressionUtil.and(e1, e2),
        ExpressionUtil.and(e2, e3)));

    Expression<Boolean> expected = ExpressionUtil.or(
        ExpressionUtil.and(e2, e3),
        ExpressionUtil.and(e1, e2),
        ExpressionUtil.and(e2, e1));

    assertEquals(simplified, expected);
  }

  @Test
  public void duplicateClausesTest5(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicateSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e1, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e1, e4),
        ExpressionUtil.or(e2, e3)));

    Expression<Boolean> expected = ExpressionUtil.and(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e1, e4),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e1, e3));

    assertEquals(simplified, expected);
  }

  @Test
  public void duplicateClausesTest6(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicateSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e1, e3),
        ExpressionUtil.or(e2, e3)));

    Expression<Boolean> expected = ExpressionUtil.and(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e1, e3),
        ExpressionUtil.or(e2, e1));

    assertEquals(simplified, expected);
  }

  @Test
  public void duplicateClausesTest10(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicateSameOperatorSequences(ExpressionUtil.or(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e1, e3),
        ExpressionUtil.or(e2, e3)));

    Expression<Boolean> expected = ExpressionUtil.or(
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e2, e3),
        ExpressionUtil.or(e2, e1),
        ExpressionUtil.or(e1, e3),
        ExpressionUtil.or(e2, e3));

    assertEquals(simplified, expected);
  }

  @Test
  public void duplicateClausesTest11(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicateSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.and(e2, e3),
        ExpressionUtil.and(e2, e1, ExpressionUtil.or(e2, e3))));

    Expression<Boolean> expected = ExpressionUtil.and(
        ExpressionUtil.and(e2, e3),
        ExpressionUtil.and(e2, e1),
        ExpressionUtil.or(e2, e3));

    System.out.println(simplified);
    System.out.println(expected);
    assertEquals(simplified, expected);
  }

  @Test
  public void duplicateClausesTest12(){
    Expression<Boolean> simplified = NormalizationUtil.removeDuplicateSameOperatorSequences(ExpressionUtil.and(
        ExpressionUtil.and(ExpressionUtil.and(e1, e2), ExpressionUtil.or(e3, e4)),
        ExpressionUtil.and(ExpressionUtil.or(e3, e4), ExpressionUtil.and(e3, e4))));

    Expression<Boolean> expected = ExpressionUtil.and(
        ExpressionUtil.and(ExpressionUtil.and(e1, e2), ExpressionUtil.or(e3, e4), ExpressionUtil.and(e3, e4)));

    System.out.println(simplified);
    System.out.println(expected);
    assertEquals(simplified, expected);
  }

  @Test
  public void quantifierCheckTest1() {
    List<Variable<?>> bound = new ArrayList<Variable<?>>();
    bound.add(x);
    Expression<Boolean> quantified = Negation.create(QuantifierExpression.create(Quantifier.EXISTS, bound, e3));
    boolean checkExpression = NormalizationUtil.quantifierCheck(quantified);

    assertTrue(checkExpression);
  }

  @Test
  public void quantifierCheckTest2() {
    List<Variable<?>> bound = new ArrayList<Variable<?>>();
    bound.add(x);
    Expression<Boolean> quantified = Negation.create(PropositionalCompound.create(QuantifierExpression.create(Quantifier.EXISTS, bound, e3), LogicalOperator.OR, negE3));
    boolean checkExpression = NormalizationUtil.quantifierCheck(quantified);

    assertTrue(checkExpression);
  }
}
