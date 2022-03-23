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

package gov.nasa.jpf.constraints.parser;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.TypeContext;
import java.util.HashSet;
import java.util.List;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

/**
 * We just want to assure that a certain set of constraints is parsable without errors
 *
 * @author Malte Mues
 */
@Tag("base")
@Tag("parser")
public class ExtendedParserTest {

  Variable<Byte> x;
  Variable<Boolean> b;
  Variable<Integer> c;
  HashSet<Variable<?>> vars;

  public ExtendedParserTest() {
    x = new Variable<>(BuiltinTypes.SINT8, "x");
    b = new Variable<>(BuiltinTypes.BOOL, "b");
    c = new Variable<>(BuiltinTypes.SINT32, "c");
    vars = new HashSet<>();
    vars.add(x);
    vars.add(c);
    vars.add(b);
  }

  @Test
  public void variableDeclarationOfPrimeVariables() throws ImpreciseRepresentationException {
    String varDeclaration = "declare x:sint8, b:bool, c:sint32";
    String primeVarDeclaration = "declare x':sint8, b':bool, c':sint32";

    List<Variable<?>> parsedVar = ParserUtil.parseVariableDeclaration(varDeclaration);
    parsedVar.addAll(ParserUtil.parseVariableDeclaration(primeVarDeclaration));
    assert (parsedVar.contains(x));
    assert (parsedVar.contains(b));
    assert (parsedVar.contains(c));

    Variable<Byte> xprime;
    Variable<Boolean> bprime;
    Variable<Integer> cprime;
    xprime = new Variable<>(BuiltinTypes.SINT8, "x'");
    bprime = new Variable<>(BuiltinTypes.BOOL, "b'");
    cprime = new Variable<>(BuiltinTypes.SINT32, "c'");
    assert (parsedVar.contains(xprime));
    assert (parsedVar.contains(bprime));
    assert (parsedVar.contains(cprime));
  }

  @Test
  public void usingPrimeVariables() throws ImpreciseRepresentationException {
    String testInput = "declare x:sint32, x':sint32 in x > 5 && x' == 5";
    Expression<Boolean> parsedRes = ParserUtil.parseLogical(testInput);
    assertEquals(parsedRes.getClass(), PropositionalCompound.class);

    testInput = "declare x':sint32 in forall (x') : (x' > 5b && (exists (c) : (c > x)))";
    parsedRes = ParserUtil.parseLogical(testInput, new TypeContext(true), vars);

    assertEquals(QuantifierExpression.class, parsedRes.getClass());
  }

  @Test
  public void variableDeclaration() throws ImpreciseRepresentationException {
    String varDeclaration = "declare x:sint8, b:bool, c:sint32";

    List<Variable<?>> parsedVar = ParserUtil.parseVariableDeclaration(varDeclaration);

    assert (parsedVar.contains(x));
    assert (parsedVar.contains(b));
    assert (parsedVar.contains(c));
  }

  @Test
  public void andBooleanExpression() throws ImpreciseRepresentationException {
    String testString = "declare x:sint8, b:bool, c:sint32 in (c == 5) && (b == false) && (x > c)";
    Expression<Boolean> expr = ParserUtil.parseLogical(testString);

    assertTrue(checkAndExpression(expr));

    testString = "declare x:sint8, b:bool, c:sint32 in c == 5 && b == false && x > c";
    expr = ParserUtil.parseLogical(testString);

    assertTrue(checkAndExpression(expr));
  }

  @Test
  public void orBooleanExpression() throws ImpreciseRepresentationException {
    // the 5b forces the parser to interpret 5 of type sint8. Otherwise an
    // undesired castexpression is added...
    String testString = "x + 5b > c || b == false";
    Expression<Boolean> expr = ParserUtil.parseLogical(testString, new TypeContext(true), vars);

    assertEquals(PropositionalCompound.class, expr.getClass());
    PropositionalCompound propCompound = (PropositionalCompound) expr;
    assertEquals(LogicalOperator.OR, propCompound.getOperator());

    PropositionalCompound assignmentB = (PropositionalCompound) propCompound.getRight();
    assertEquals(b, assignmentB.getLeft());
    assertEquals(LogicalOperator.EQUIV, assignmentB.getOperator());

    assertEquals(NumericBooleanExpression.class, propCompound.getLeft().getClass());
    NumericBooleanExpression comparisonC = (NumericBooleanExpression) propCompound.getLeft();
    assertEquals(NumericComparator.GT, comparisonC.getComparator());
    assertEquals(c, comparisonC.getRight());

    assertEquals(NumericCompound.class, comparisonC.getLeft().getClass());
    NumericCompound additionX = (NumericCompound) comparisonC.getLeft();

    Variable parsedX = (Variable) additionX.getLeft();

    assertEquals(x.getType(), parsedX.getType());
    assertEquals(x.getName(), parsedX.getName());
    assertEquals(x, additionX.getLeft());
    assertEquals(Constant.class, additionX.getRight().getClass());
    assertEquals(NumericOperator.PLUS, additionX.getOperator());
  }

  private boolean checkAndExpression(Expression<Boolean> expr) {
    assertEquals(PropositionalCompound.class, expr.getClass());
    PropositionalCompound propCompound = (PropositionalCompound) expr;
    assertEquals(NumericBooleanExpression.class, propCompound.getRight().getClass());
    assertEquals(LogicalOperator.AND, propCompound.getOperator());
    assertEquals(PropositionalCompound.class, propCompound.getLeft().getClass());

    NumericBooleanExpression comparisonXC = (NumericBooleanExpression) propCompound.getRight();
    propCompound = (PropositionalCompound) propCompound.getLeft();

    assertEquals(x, comparisonXC.getLeft());
    assertEquals(c, comparisonXC.getRight());
    assertEquals(NumericComparator.GT, comparisonXC.getComparator());

    NumericBooleanExpression assignmentC = (NumericBooleanExpression) propCompound.getLeft();
    assertEquals(c, assignmentC.getLeft());
    assertEquals(NumericComparator.EQ, assignmentC.getComparator());

    PropositionalCompound assignmentB = (PropositionalCompound) propCompound.getRight();
    assertEquals(b, assignmentB.getLeft());
    assertEquals(LogicalOperator.EQUIV, assignmentB.getOperator());
    return true;
  }

  @Test
  public void quantifierExpression() throws ImpreciseRepresentationException {
    String testString = "forall (x) : (x > 5b && (exists (c) : (c > x)))";

    Expression<Boolean> expr = ParserUtil.parseLogical(testString, new TypeContext(true), vars);

    assertEquals(QuantifierExpression.class, expr.getClass());
    QuantifierExpression allQuantifiedExpr = (QuantifierExpression) expr;
    assertEquals(Quantifier.FORALL, allQuantifiedExpr.getQuantifier());
    assertEquals(1, allQuantifiedExpr.getBoundVariables().size());
    assertEquals(x, allQuantifiedExpr.getBoundVariables().get(0));

    assertEquals(PropositionalCompound.class, allQuantifiedExpr.getBody().getClass());
    PropositionalCompound propCompound = (PropositionalCompound) allQuantifiedExpr.getBody();

    assertEquals(QuantifierExpression.class, propCompound.getRight().getClass());
    QuantifierExpression existQuantifiedExpr = (QuantifierExpression) propCompound.getRight();
    assertEquals(Quantifier.EXISTS, existQuantifiedExpr.getQuantifier());
    assertEquals(1, existQuantifiedExpr.getBoundVariables().size());
    assertEquals(c, existQuantifiedExpr.getBoundVariables().get(0));
  }

  @Test
  public void undeclaredVarInQuantifiedExpression() {
    String testString = "forall (y:sint32) : (exists (a) : (x > 5b && c > 3))";
    assertThrows(
        UndeclaredVariableException.class,
        () -> ParserUtil.parseLogical(testString, new TypeContext(true), vars));
  }

  @Test
  public void wrongEQ() {
    String testString = "declare x:sint32 in x = 5";
    assertThrows(AntlrException.class, () -> ParserUtil.parseLogical(testString));
  }
}
