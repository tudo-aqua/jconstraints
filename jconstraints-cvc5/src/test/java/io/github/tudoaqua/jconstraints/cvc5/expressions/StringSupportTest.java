/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2023 The jConstraints Authors
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

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
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
import io.github.tudoaqua.jconstraints.cvc5.AbstractCVC5Test;
import io.github.tudoaqua.jconstraints.cvc5.CVC5Solver;
import java.io.IOException;
import java.math.BigInteger;
import java.util.LinkedList;
import java.util.List;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

public class StringSupportTest extends AbstractCVC5Test {

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
  @Disabled // Currently, this is DONT_KNOW Recheck later FIXME
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

  @Test
  public void stringInReTest() {
    Constant<String> c = Constant.create(BuiltinTypes.STRING, "av");
    RegExBooleanExpression rbe =
        RegExBooleanExpression.create(
            c, RegexOperatorExpression.createLoop(RegexOperatorExpression.createAllChar(), 1, 1));
    Expression<Boolean> expr1 = PropositionalCompound.create(rbe, EQUIV, ExpressionUtil.TRUE);
    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(expr1, val);
    assertEquals(UNSAT, res);
  }

  @Test
  public void strToCodePointTest() throws IOException, SMTLIBParserException {
    String input =
        "(declare-fun __string_0 () String) (assert (bvsle ((_ int2bv 32) (str.to_code (str.at"
            + " __string_0 (bv2int #x00000000)))) #x000003e8))(assert (bvsge ((_ int2bv 32)"
            + " (str.to_code (str.at __string_0 (bv2int #x00000000)))) #x00000000))";
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

  @Test
  public void exampleTest() throws IOException, SMTLIBParserException {
    ConstraintSolver unsatCoreSolver = new CVC5Solver();
    SolverContext ctx = unsatCoreSolver.createContext();
    String problem =
        "(declare-fun beginWord () String)\n"
            + "(declare-fun endWord () String)\n"
            + "\n"
            + "(assert (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and"
            + " (and (and (and (and (and (and (and (and (and (and (and (and (and (not (not (not (="
            + " (ite (= (str.++ (str.++ (str.substr (str.++ (str.++ (str.substr beginWord 0 (- 1"
            + " 0)) \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2))) 0 (- 0 0)) \"l\")"
            + " (str.substr (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr"
            + " beginWord 2 (- (str.len beginWord) 2))) 1 (- (str.len (str.++ (str.++ (str.substr"
            + " beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2))))"
            + " 1))) endWord) 1 0) 0)))) (not (= (ite (= endWord endWord) 1 0) 0))) (not (not (="
            + " (ite (= (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1"
            + " (- (str.len endWord) 1))) endWord) 1 0) 0)))) (not (= (ite (= (str.++ (str.++"
            + " (str.substr (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr"
            + " endWord 1 (- (str.len endWord) 1))) 0 (- 2 0)) \"t\") (str.substr (str.++ (str.++"
            + " (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len endWord)"
            + " 1))) 3 (- (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\")"
            + " (str.substr endWord 1 (- (str.len endWord) 1)))) 3))) (str.++ (str.++ (str.substr"
            + " (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (-"
            + " (str.len beginWord) 2))) 0 (- 0 0)) \"d\") (str.substr (str.++ (str.++ (str.substr"
            + " beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2))) 1"
            + " (- (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr"
            + " beginWord 2 (- (str.len beginWord) 2)))) 1)))) 1 0) 0))) (not (not (= (ite (="
            + " (str.++ (str.++ (str.substr (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2))) 0 (- 0 0)) \"d\") (str.substr"
            + " (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (-"
            + " (str.len beginWord) 2))) 1 (- (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1"
            + " 0)) \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2)))) 1))) endWord) 1 0)"
            + " 0)))) (not (not (= (ite (= (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2))) endWord) 1 0) 0)))) (not (not"
            + " (= (ite (= beginWord endWord) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++"
            + " (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len"
            + " endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len endWord)"
            + " 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr"
            + " endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0))"
            + " \"d\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr"
            + " endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len"
            + " (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (-"
            + " (str.len endWord) 1)))) 0) 1 0) 0)))) (not (= (ite (= (str.++ (str.++ (str.substr"
            + " (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (-"
            + " (str.len beginWord) 2))) 0 (- 0 0)) \"d\") (str.substr (str.++ (str.++ (str.substr"
            + " beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2))) 1"
            + " (- (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr"
            + " beginWord 2 (- (str.len beginWord) 2)))) 1))) (str.++ (str.++ (str.substr (str.++"
            + " (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len"
            + " endWord) 1))) 0 (- 2 0)) \"t\") (str.substr (str.++ (str.++ (str.substr endWord 0"
            + " (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len endWord) 1))) 3 (- (str.len"
            + " (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (-"
            + " (str.len endWord) 1)))) 3)))) 1 0) 0))) (not (not (= (ite (<= (str.len (str.++"
            + " (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len"
            + " endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len endWord)"
            + " 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr"
            + " endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0))"
            + " \"d\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr"
            + " endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len"
            + " (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (-"
            + " (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++"
            + " (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len"
            + " endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len endWord)"
            + " 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr"
            + " endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0))"
            + " \"d\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr"
            + " endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len"
            + " (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (-"
            + " (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++"
            + " (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len"
            + " endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len endWord)"
            + " 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr"
            + " endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0))"
            + " \"d\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr"
            + " endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len"
            + " (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (-"
            + " (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++"
            + " (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len"
            + " endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len endWord)"
            + " 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr"
            + " endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0))"
            + " \"l\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr"
            + " endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len"
            + " (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (-"
            + " (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++"
            + " (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len"
            + " endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord)"
            + " 1)))) 0) 1 0) 0)))) (not (= (ite (= (str.++ (str.++ (str.substr (str.++ (str.++"
            + " (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2))) 0 (- 0 0)) \"l\") (str.substr (str.++ (str.++ (str.substr beginWord"
            + " 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2))) 1 (- (str.len"
            + " (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (-"
            + " (str.len beginWord) 2)))) 1))) (str.++ (str.++ (str.substr (str.++ (str.++"
            + " (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord)"
            + " 1))) 0 (- 2 0)) \"t\") (str.substr (str.++ (str.++ (str.substr endWord 0 (- 0 0))"
            + " \"l\") (str.substr endWord 1 (- (str.len endWord) 1))) 3 (- (str.len (str.++"
            + " (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len"
            + " endWord) 1)))) 3)))) 1 0) 0))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord)"
            + " 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr"
            + " endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0))"
            + " \"l\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr"
            + " endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len"
            + " (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (-"
            + " (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++"
            + " (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len"
            + " endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord)"
            + " 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr"
            + " endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0))"
            + " \"l\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr"
            + " endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len"
            + " (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (-"
            + " (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++"
            + " (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len"
            + " endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord)"
            + " 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr"
            + " endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0))"
            + " \"l\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr"
            + " endWord 1 (- (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len"
            + " (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (-"
            + " (str.len endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++"
            + " (str.++ (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len"
            + " endWord) 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord)"
            + " 1)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr"
            + " endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord) 1)))) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len endWord) 0) 1 0) 0)))) (not (= (ite (= (str.++ (str.++ (str.substr endWord"
            + " 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord) 1))) \"log\") 1 0)"
            + " 0))) (not (= (ite (= (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"l\")"
            + " (str.substr endWord 1 (- (str.len endWord) 1))) \"log\") 1 0) 0))) (not (not (="
            + " (ite (<= (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len endWord) 0)"
            + " 1 0) 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite"
            + " (<= (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0)"
            + " 0)))) (not (= (ite (= (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\")"
            + " (str.substr endWord 1 (- (str.len endWord) 1))) \"dog\") 1 0) 0))) (not (= (ite (="
            + " (str.++ (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (-"
            + " (str.len endWord) 1))) \"dog\") 1 0) 0))) (not (not (= (ite (<= (str.len endWord)"
            + " 0) 1 0) 0)))) (not (not (= (ite (<= (str.len endWord) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len endWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len endWord) 0)"
            + " 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0"
            + " (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0))))"
            + " (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0))"
            + " \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not"
            + " (= (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (= (ite (="
            + " (str.++ (str.++ (str.substr (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2))) 0 (- 0 0)) \"l\") (str.substr"
            + " (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (-"
            + " (str.len beginWord) 2))) 1 (- (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1"
            + " 0)) \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2)))) 1))) \"lot\") 1 0)"
            + " 0))) (not (= (ite (= (str.++ (str.++ (str.substr (str.++ (str.++ (str.substr"
            + " beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2))) 0"
            + " (- 0 0)) \"l\") (str.substr (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2))) 1 (- (str.len (str.++ (str.++"
            + " (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2)))) 1))) \"lot\") 1 0) 0))) (not (not (= (ite (<= (str.len (str.++"
            + " (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2)))) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len (str.++ (str.++"
            + " (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2)))) 0) 1 0) 0)))) (not (= (ite (= (str.++ (str.++ (str.substr (str.++"
            + " (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2))) 0 (- 0 0)) \"d\") (str.substr (str.++ (str.++ (str.substr beginWord"
            + " 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2))) 1 (- (str.len"
            + " (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (-"
            + " (str.len beginWord) 2)))) 1))) \"dot\") 1 0) 0))) (not (= (ite (= (str.++ (str.++"
            + " (str.substr (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr"
            + " beginWord 2 (- (str.len beginWord) 2))) 0 (- 0 0)) \"d\") (str.substr (str.++"
            + " (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2))) 1 (- (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0))"
            + " \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2)))) 1))) \"dot\") 1 0) 0)))"
            + " (not (not (= (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0))"
            + " \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not"
            + " (= (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 0) 1 0) 0)))) (not (not (="
            + " (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len"
            + " beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0))))"
            + " (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len beginWord) 0) 1 0) 0)))) (not (= (ite (= (str.++ (str.++ (str.substr"
            + " beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2)))"
            + " \"hot\") 1 0) 0))) (not (= (ite (= (str.++ (str.++ (str.substr beginWord 0 (- 1 0))"
            + " \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2))) \"hot\") 1 0) 0))) (not"
            + " (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len"
            + " beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0))))"
            + " (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0)"
            + " 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<="
            + " (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0)"
            + " 0)))) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0"
            + " 0)) (>= (- 0 0) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord)"
            + " 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 1"
            + " 0)) (>= (- (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\")"
            + " (str.substr beginWord 2 (- (str.len beginWord) 2)))) 1) 0)) (>= 0 0)) (>= (- 0 0)"
            + " 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0))"
            + " (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 2 0) 0)) (>= 0 0)) (>= (- 0 0) 0))"
            + " (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>="
            + " (- (str.len endWord) 1) 0)) (>= 3 0)) (>= (- (str.len (str.++ (str.++ (str.substr"
            + " endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len endWord) 1)))) 3) 0))"
            + " (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>="
            + " (- 0 0) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0))"
            + " (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 1 0)) (>="
            + " (- (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr"
            + " beginWord 2 (- (str.len beginWord) 2)))) 1) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0))"
            + " (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 0 0)) (>= (- 1 0)"
            + " 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0))"
            + " (>= (- (str.len beginWord) 2) 0)) (>= 1 0)) (>= (- (str.len (str.++ (str.++"
            + " (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2)))) 1) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len"
            + " beginWord) 2) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1)"
            + " 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0))"
            + " (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0))"
            + " (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>="
            + " (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len"
            + " endWord) 1) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2)"
            + " 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len"
            + " beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2)"
            + " 0)) (>= 1 0)) (>= (- (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0))"
            + " \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2)))) 1) 0)) (>= 0 0)) (>= (-"
            + " 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 2 0) 0)) (>= 0"
            + " 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0)"
            + " 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 3 0)) (>= (- (str.len (str.++"
            + " (str.++ (str.substr endWord 0 (- 0 0)) \"d\") (str.substr endWord 1 (- (str.len"
            + " endWord) 1)))) 3) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord)"
            + " 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0"
            + " 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0)"
            + " 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0))"
            + " (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len"
            + " endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0))"
            + " (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>="
            + " (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>="
            + " 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (-"
            + " (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len"
            + " endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0))"
            + " (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>="
            + " (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>="
            + " 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (-"
            + " (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len"
            + " endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0))"
            + " (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>="
            + " (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>="
            + " 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (-"
            + " (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len"
            + " endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0))"
            + " (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>="
            + " (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 0 0) 0))"
            + " (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>="
            + " (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 1 0)) (>= (- (str.len"
            + " (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (-"
            + " (str.len beginWord) 2)))) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (-"
            + " (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 2 0) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1"
            + " 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (-"
            + " (str.len endWord) 1) 0)) (>= 3 0)) (>= (- (str.len (str.++ (str.++ (str.substr"
            + " endWord 0 (- 0 0)) \"l\") (str.substr endWord 1 (- (str.len endWord) 1)))) 3) 0))"
            + " (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>="
            + " (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>="
            + " 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (-"
            + " (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len"
            + " endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0))"
            + " (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>="
            + " (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>="
            + " 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (-"
            + " (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len"
            + " endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0))"
            + " (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>="
            + " (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>="
            + " 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (-"
            + " (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len"
            + " endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0))"
            + " (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>="
            + " (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>="
            + " 1 0)) (>= (- (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (-"
            + " (str.len endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len"
            + " endWord) 1) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 1 0)) (>= (- (str.len endWord) 1) 0))"
            + " (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>="
            + " (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0))"
            + " (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>="
            + " (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len"
            + " beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2)"
            + " 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0))"
            + " (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0)"
            + " 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0))"
            + " (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (-"
            + " (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len"
            + " beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2)"
            + " 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0))"
            + " (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 0 0)"
            + " 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0))"
            + " (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 1 0)) (>= (-"
            + " (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr"
            + " beginWord 2 (- (str.len beginWord) 2)))) 1) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0))"
            + " (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 0 0)) (>= (- 1 0)"
            + " 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0))"
            + " (>= (- (str.len beginWord) 2) 0)) (>= 1 0)) (>= (- (str.len (str.++ (str.++"
            + " (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (- (str.len"
            + " beginWord) 2)))) 1) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len"
            + " beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2)"
            + " 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0))"
            + " (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0)"
            + " 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0))"
            + " (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (-"
            + " (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len"
            + " beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2)"
            + " 0)) (>= 0 0)) (>= (- 0 0) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len"
            + " beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2)"
            + " 0)) (>= 1 0)) (>= (- (str.len (str.++ (str.++ (str.substr beginWord 0 (- 1 0))"
            + " \"o\") (str.substr beginWord 2 (- (str.len beginWord) 2)))) 1) 0)) (>= 0 0)) (>= (-"
            + " 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 0 0) 0)) (>="
            + " 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (-"
            + " 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 1 0)) (>= (- (str.len"
            + " (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) \"o\") (str.substr beginWord 2 (-"
            + " (str.len beginWord) 2)))) 1) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (-"
            + " (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len"
            + " beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2)"
            + " 0)) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0))"
            + " (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)) (>= 0 0)) (>= (- 1 0)"
            + " 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)))\n"
            + "\n"
            + "(check-sat)";
    SMTProblem pProblem = SMTLIBParser.parseSMTProgram(problem);
    ctx.add(pProblem.getAllAssertionsAsConjunction());

    Valuation val = new Valuation();
    Result res = ctx.solve(val);
    assertEquals(res, Result.UNSAT);
  }

  @Test
  public void toUpperEvaluation() throws IOException, SMTLIBParserException {
    String program =
        "(declare-fun __string_0 () String)"
            + "(assert (not (str.contains (str.upper __string_0) \"<bad/>\")))"
            + "(assert (not (str.contains __string_0 \"<bad/>\")))";
    SMTProblem pProblem = SMTLIBParser.parseSMTProgram(program);

    Valuation val = new Valuation();
    Result res = cvc5.solve(pProblem.getAllAssertionsAsConjunction(), val);
    assertEquals(res, Result.SAT);
    assertTrue(pProblem.getAllAssertionsAsConjunction().evaluateSMT(val));
  }

  @Test
  public void strCodeTest() throws IOException, SMTLIBParserException {
    String input =
        "(declare-const __string_0 String)\n"
            + "(assert (bvsle #x00000001 ((_ int2bv 32) (str.len __string_0))))\n"
            + "(assert (bvslt #x00000000 ((_ int2bv 32) (str.len __string_0))))\n"
            + "(assert (not (bvslt ((_ int2bv 32) (str.to_code (str.at __string_0 (ite (bvslt"
            + " #x00000000 #x00000000) (- (bv2nat #x00000000)) (bv2nat #x00000000)))))"
            + " #x00000000)))\n"
            + "(assert (not (bvsge #x0000ffff ((_ int2bv 32) (str.to_code (str.at __string_0 (ite"
            + " (bvslt #x00000000 #x00000000) (- (bv2nat #x00000000)) (bv2nat #x00000000))))))))\n"
            + "(assert (and true (<= (str.len __string_0) 60)))\n"
            + "(check-sat)";
    SMTProblem problem = SMTLIBParser.parseSMTProgram(input);
    Valuation val = new Valuation();
    Result res = cvc5.solve(problem.getAllAssertionsAsConjunction(), val);
    assertEquals(res, SAT);
  }
}
