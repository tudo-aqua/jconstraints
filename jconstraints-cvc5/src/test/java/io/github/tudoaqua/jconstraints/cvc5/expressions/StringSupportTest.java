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

package io.github.tudoaqua.jconstraints.cvc5.expressions;

import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.SAT;
import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.UNSAT;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.AND;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.EQUIV;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.IMPLY;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.LE;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.LT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.NE;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import edu.stanford.CVC4.CVC4String;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.SmtEngine;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
import gov.nasa.jpf.constraints.expressions.RegexOperatorExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringCompoundExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import io.github.tudoaqua.jconstraints.cvc5.AbstractCVC4Test;
import java.io.IOException;
import java.math.BigInteger;
import java.util.LinkedList;
import java.util.List;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

public class StringSupportTest extends AbstractCVC4Test {

  @Test
  public void strLenTest() {
    Constant<Integer> c5 = Constant.create(BuiltinTypes.SINT32, 5);
    Variable<String> string = Variable.create(BuiltinTypes.STRING, "x1");
    Expression<BigInteger> len = StringIntegerExpression.createLength(string);
    Expression<Integer> len2 = CastExpression.create(len, BuiltinTypes.SINT32);
    NumericBooleanExpression compLen =
        NumericBooleanExpression.create(len2, NumericComparator.EQ, c5);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(compLen, val);
    assertEquals(res, SAT);
    if (res == SAT) {
      assertTrue(compLen.evaluate(val));
    }
  }

  @Test
  public void strLen2Test() {
    Constant<Integer> c5 = Constant.create(BuiltinTypes.SINT32, 5);
    Variable<String> string = Variable.create(BuiltinTypes.STRING, "x1");
    Expression<BigInteger> len = StringIntegerExpression.createLength(string);
    Expression<Integer> len2 = CastExpression.create(len, BuiltinTypes.SINT32);
    NumericBooleanExpression compLen =
        NumericBooleanExpression.create(len2, NumericComparator.EQ, c5);

    Constant<String> cHallo = Constant.create(BuiltinTypes.STRING, "Hallo");
    StringBooleanExpression strEq = StringBooleanExpression.createEquals(string, cHallo);

    Expression<Boolean> finalExpr =
        PropositionalCompound.create(compLen, LogicalOperator.AND, strEq);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(finalExpr, val);
    assertEquals(res, SAT);
    boolean equals = compLen.evaluate(val);
    assertTrue(equals);
  }

  @Test
  public void autoCastStrAtTest() {
    Constant<Integer> c4 = Constant.create(BuiltinTypes.SINT32, 5);
    Variable<String> strVar = Variable.create(BuiltinTypes.STRING, "string0");
    Expression<String> stringAt = StringCompoundExpression.createAt(strVar, c4);
    Constant<String> stringExpected = Constant.create(BuiltinTypes.STRING, "c");
    Expression<Boolean> stringAt2 = StringBooleanExpression.createEquals(stringAt, stringExpected);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(stringAt2, val);
    assertEquals(res, SAT);
    boolean equals = stringAt2.evaluate(val);
    assertTrue(equals);
  }

  @Test
  public void castStringLen() {
    Constant<Integer> c_1 = Constant.create(BuiltinTypes.SINT32, 1);

    Variable<String> strVar = Variable.create(BuiltinTypes.STRING, "string0");
    Constant<String> cCase1 = Constant.create(BuiltinTypes.STRING, "case1");

    StringBooleanExpression eqExpr = StringBooleanExpression.createEquals(strVar, cCase1);
    CastExpression<BigInteger, Integer> castedStringExpression =
        CastExpression.create(StringIntegerExpression.createLength(strVar), BuiltinTypes.SINT32);
    NumericBooleanExpression lenEqExpr =
        NumericBooleanExpression.create(castedStringExpression, NE, UnaryMinus.create(c_1));
    cvc5Context.add(eqExpr);
    cvc5Context.add(lenEqExpr);

    ConstraintSolver.Result res = cvc5Context.isSatisfiable();
    assertEquals(res, SAT);
  }

  @Test
  public void toLowerCaseTest() {
    Variable<String> var = Variable.create(BuiltinTypes.STRING, "x");
    Constant<String> cU = Constant.create(BuiltinTypes.STRING, "UpperCase");
    Constant<String> target = Constant.create(BuiltinTypes.STRING, "uppercase");

    StringBooleanExpression part1 = StringBooleanExpression.createEquals(var, cU);
    StringCompoundExpression lower = StringCompoundExpression.createToLower(var);
    StringBooleanExpression part2 = StringBooleanExpression.createEquals(lower, target);
    PropositionalCompound complete = PropositionalCompound.create(part1, AND, part2);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(complete, val);
    assertEquals(res, SAT);
    assertTrue(complete.evaluate(val));
  }

  @Test
  public void toUpperCaseTest() {
    Variable<String> var = Variable.create(BuiltinTypes.STRING, "x");
    Constant<String> cU = Constant.create(BuiltinTypes.STRING, "uppercase");
    Constant<String> target = Constant.create(BuiltinTypes.STRING, "UPPERCASE");

    StringBooleanExpression part1 = StringBooleanExpression.createEquals(var, cU);
    StringCompoundExpression upper = StringCompoundExpression.createToUpper(var);
    StringBooleanExpression part2 = StringBooleanExpression.createEquals(upper, target);
    PropositionalCompound complete = PropositionalCompound.create(part1, AND, part2);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(complete, val);
    assertEquals(res, SAT);
    assertTrue(complete.evaluate(val));
  }

  @Test
  public void toAndFromIntEvaluationTest() {
    Variable<String> x = Variable.create(BuiltinTypes.STRING, "x");
    Constant<String> c = Constant.create(BuiltinTypes.STRING, "10");
    Expression<BigInteger> toInt = StringIntegerExpression.createToInt(x);
    Expression<String> fromInt = StringCompoundExpression.createToString(toInt);
    StringBooleanExpression equals = StringBooleanExpression.createEquals(fromInt, c);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(equals, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(equals.evaluate(val));
  }

  @Test
  public void conversionTest() {
    // this test case models: (='_string2'(str.at '_string0' (integer)((sint32)(str.len '_string0')
    // - 1)) )

    Variable<String> string1 = Variable.create(BuiltinTypes.STRING, "string0");
    Variable<String> string2 = Variable.create(BuiltinTypes.STRING, "string2");

    StringIntegerExpression string1Len = StringIntegerExpression.createLength(string1);

    Expression<Integer> castedString1Len = CastExpression.create(string1Len, BuiltinTypes.SINT32);
    Expression<Boolean> stringExists =
        NumericBooleanExpression.create(
            castedString1Len, GT, Constant.create(BuiltinTypes.SINT32, 5));
    Expression<Integer> arithmetik =
        NumericCompound.create(
            castedString1Len, NumericOperator.MINUS, Constant.create(BuiltinTypes.SINT32, 1));
    Expression<BigInteger> castBack = CastExpression.create(arithmetik, BuiltinTypes.INTEGER);
    Expression<String> charAt = StringCompoundExpression.createAt(string1, castBack);
    Expression<Boolean> equals = StringBooleanExpression.createEquals(string2, charAt);

    Expression<Boolean> complete = PropositionalCompound.create(stringExists, AND, equals);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(complete, val);
    assertEquals(res, SAT);
    assertTrue(complete.evaluate(val));
  }

  @Test
  public void strIndexOf1() {
    Variable<String> str = Variable.create(BuiltinTypes.STRING, "str");
    Constant<String> c = Constant.create(BuiltinTypes.STRING, "/");

    Expression<BigInteger> complete = StringIntegerExpression.createIndexOf(str, c);
    Expression<Boolean> complete2 =
        NumericBooleanExpression.create(
            complete, NE, Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(-1L)));
    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(complete2, val);
    assertEquals(res, SAT);
  }

  @Test
  public void strLastIndexOf1() {
    Variable<BigInteger> x = Variable.create(BuiltinTypes.INTEGER, "x");
    Variable<String> a = Variable.create(BuiltinTypes.STRING, "a");
    Constant<String> b = Constant.create(BuiltinTypes.STRING, "b");
    Constant<BigInteger> ten = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(10));
    Constant<BigInteger> hundred = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(100));
    Variable<BigInteger> boundedC = Variable.create(BuiltinTypes.INTEGER, "c");
    List<Variable<?>> boundedVars = new LinkedList<>();
    boundedVars.add(boundedC);

    Expression<Boolean> part1 =
        NumericBooleanExpression.create(StringIntegerExpression.createLength(a), GT, ten);
    Expression<Boolean> part2 =
        NumericBooleanExpression.create(StringIntegerExpression.createLength(a), LT, hundred);
    Expression<Boolean> part3 =
        StringBooleanExpression.createEquals(b, StringCompoundExpression.createAt(a, x));
    Expression<Boolean> part4 =
        PropositionalCompound.create(
            NumericBooleanExpression.create(boundedC, GT, x),
            AND,
            NumericBooleanExpression.create(boundedC, LE, StringIntegerExpression.createLength(a)));
    Expression<Boolean> part5 =
        Negation.create(
            StringBooleanExpression.createEquals(
                b, StringCompoundExpression.createAt(a, boundedC)));
    Expression<Boolean> imply = PropositionalCompound.create(part4, IMPLY, part5);
    Expression<Boolean> forall = new QuantifierExpression(Quantifier.FORALL, boundedVars, imply);
    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(ExpressionUtil.and(part1, part2, part3, forall), val);
    assertEquals(res, SAT);
    assertTrue(part1.evaluate(val));
    assertTrue(part2.evaluate(val));
    assertTrue(part3.evaluate(val));
  }

  @Test
  public void stringToReTest() {
    Variable<String> a = Variable.create(BuiltinTypes.STRING, "a");
    Variable<String> regex = Variable.create(BuiltinTypes.STRING, "reg");
    RegexOperatorExpression convRegex = RegexOperatorExpression.createStrToRe(regex);
    RegExBooleanExpression inRegex = RegExBooleanExpression.create(a, convRegex);
    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(inRegex, val);
    assertEquals(res, SAT);
    inRegex.evaluate(val);
  }

  // FIXME: This seems to be a problem in the JAVA API??? (assert (str.in_re "av" re.allchar)) works
  // on commandline.
  @Test
  @Disabled
  public void stringInReNativeTest() {
    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);
    Expr c1 = em.mkConst(new CVC4String("av"));
    Expr allchar = em.mkConst(Kind.REGEXP_SIGMA);
    Expr expr = em.mkExpr(Kind.STRING_IN_REGEXP, c1, allchar);
    String res = smt.checkSat(expr).toString();
    assertEquals("unsat", res);

    c1.delete();
    allchar.delete();
    expr.delete();
    smt.delete();
    em.delete();
  }

  // We run it with the CVC4SMTCMDSolver in replacement.
  @Test
  public void stringInReTest() {
    Constant<String> c = Constant.create(BuiltinTypes.STRING, "av");
    RegExBooleanExpression rbe =
        RegExBooleanExpression.create(
            c, RegexOperatorExpression.createLoop(RegexOperatorExpression.createAllChar(), 1, 1));
    Expression<Boolean> expr1 = PropositionalCompound.create(rbe, EQUIV, ExpressionUtil.TRUE);
    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(expr1, val);
    assertEquals(res, UNSAT);
  }

  @Test
  public void strToCodePointTest() throws IOException, SMTLIBParserException {
    String input =
        "(declare-fun __string_0 () String) (assert (bvsle ((_ int2bv 32) (str.to_code (str.at __string_0 (bv2int #x00000000)))) #x000003e8))"
            + "(assert (bvsge ((_ int2bv 32) (str.to_code (str.at __string_0 (bv2int #x00000000)))) #x00000000))";
    SMTProblem problem = SMTLIBParser.parseSMTProgram(input);
    Valuation val = new Valuation();
    Result res = cvc5.solve(problem.getAllAssertionsAsConjunction(), val);
    assertEquals(res, SAT);
    assertTrue(problem.getAllAssertionsAsConjunction().evaluate(val));
  }

  @Test
  public void strLTTest() throws IOException, SMTLIBParserException {
    String input =
        "(declare-fun __string_0 () String) (assert (str.< __string_0 \"comparisonTest\"))";
    SMTProblem problem = SMTLIBParser.parseSMTProgram(input);
    Valuation val = new Valuation();
    Result res = cvc5.solve(problem.getAllAssertionsAsConjunction(), val);
    assertEquals(res, SAT);
    assertTrue(problem.getAllAssertionsAsConjunction().evaluate(val));
  }
}
