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

package gov.nasa.jpf.constraints.expressions;

import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.SAT;
import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.UNSAT;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import java.math.BigInteger;
import java.util.Properties;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class StringSupportTest {

  private NativeZ3Solver solver;

  @BeforeEach
  public void initialize() {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    conf.setProperty("z3.options", "smt.string_solver=seq");
    solver = (NativeZ3Solver) ConstraintSolverFactory.createSolver("z3", conf);
  }

  @Test
  public void strLenTest() {
    Constant<Integer> c5 = Constant.create(BuiltinTypes.SINT32, 5);
    Variable<String> string = Variable.create(BuiltinTypes.STRING, "x1");
    Expression<BigInteger> len = StringIntegerExpression.createLength(string);
    Expression<Integer> len2 = CastExpression.create(len, BuiltinTypes.SINT32);
    NumericBooleanExpression compLen =
        NumericBooleanExpression.create(len2, NumericComparator.EQ, c5);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = solver.solve(compLen, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    if (res == ConstraintSolver.Result.SAT) {
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
    ConstraintSolver.Result res = solver.solve(finalExpr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
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
    ConstraintSolver.Result res = solver.solve(stringAt2, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    boolean equals = stringAt2.evaluate(val);
    assertTrue(equals);
  }

  @Test
  public void toAndFromIntEvaluationTest() {
    Variable<String> x = Variable.create(BuiltinTypes.STRING, "x");
    Constant<String> c = Constant.create(BuiltinTypes.STRING, "10");
    Expression<java.math.BigInteger> toInt = StringIntegerExpression.createToInt(x);
    Expression<String> fromInt = StringCompoundExpression.createToString(toInt);
    StringBooleanExpression equals = StringBooleanExpression.createEquals(fromInt, c);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = solver.solve(equals, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(equals.evaluate(val));
  }

  @Test
  public void stringInReTest() {
    Constant<String> c = Constant.create(BuiltinTypes.STRING, "av");
    RegExBooleanExpression rbe =
        RegExBooleanExpression.create(c, RegexOperatorExpression.createAllChar());
    Valuation val = new Valuation();
    ConstraintSolver.Result res = solver.solve(rbe, val);
    assertEquals(res, UNSAT);
  }

  @Test
  public void concatTest() {
    Variable<String> a = Variable.create(BuiltinTypes.STRING, "a");
    Variable<String> b = Variable.create(BuiltinTypes.STRING, "b");
    Variable<String> c = Variable.create(BuiltinTypes.STRING, "c");
    Expression<String> sce = StringCompoundExpression.createConcat(a, b, c);
    Expression<Boolean> sbe =
        StringBooleanExpression.createEquals(sce, Constant.create(BuiltinTypes.STRING, "hallo"));
    Valuation val = new Valuation();
    ConstraintSolver.Result res = solver.solve(sbe, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(sbe.evaluate(val));
  }

  @Test
  public void concat2Test() {
    Constant<String> a = Constant.create(BuiltinTypes.STRING, "ha");
    Constant<String> b = Constant.create(BuiltinTypes.STRING, "ll");
    Constant<String> c = Constant.create(BuiltinTypes.STRING, "o");
    Expression<String> sce = StringCompoundExpression.createConcat(a, b, c);
    Expression<Boolean> sbe =
        StringBooleanExpression.createEquals(sce, Constant.create(BuiltinTypes.STRING, "hallo"));
    Valuation val = new Valuation();
    ConstraintSolver.Result res = solver.solve(sbe, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(sbe.evaluate(val));
  }

  @Test
  public void concat3Test() {
    Variable<String> a = Variable.create(BuiltinTypes.STRING, "a");
    Variable<String> b = Variable.create(BuiltinTypes.STRING, "b");
    Constant<String> c = Constant.create(BuiltinTypes.STRING, "o");
    Expression<String> sce = StringCompoundExpression.createConcat(a, b, c);
    Expression<Boolean> sbe =
        StringBooleanExpression.createEquals(sce, Constant.create(BuiltinTypes.STRING, "hallo"));
    Valuation val = new Valuation();
    ConstraintSolver.Result res = solver.solve(sbe, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(sbe.evaluate(val));
  }

  @Test()
  public void strLTTest() throws IOException, SMTLIBParserException {
    Assertions.assertThrows(
        UnsupportedOperationException.class,
        () -> {
          String input =
              "(declare-fun __string_0 () String) (assert (str.< __string_0 \"comparisonTest\"))";
          SMTProblem problem = SMTLIBParser.parseSMTProgram(input);
          Valuation val = new Valuation();
          Result res = solver.solve(problem.getAllAssertionsAsConjunction(), val);
          assertEquals(res, SAT);
          assertTrue(problem.getAllAssertionsAsConjunction().evaluate(val));
        });
  }

  @Test
  public void strCodeTest() throws IOException, SMTLIBParserException {
    String input = "(declare-const x String)(assert (< (str.to_code (str.at x 0)) 0))";
    SMTProblem problem = SMTLIBParser.parseSMTProgram(input);
    Valuation val = new Valuation();
    Result res = solver.solve(problem.getAllAssertionsAsConjunction(), val);
    assertEquals(res, UNSAT);
  }
  //	@Test
  //	public void nativeConcatTest() {
  //		Context ctx = new Context();
  //		Expr<SeqSort<BitVecSort>> a = ctx.mkConst("a", ctx.getStringSort());
  //		Expr<SeqSort<BitVecSort>> b = ctx.mkConst("b", ctx.getStringSort());
  //		SeqExpr<BitVecSort> constant = ctx.mkString("test");
  //		Expr concat = ctx.mkConcat(a, b);
  //		Expr eq = ctx.mkEq(concat, constant);
  //		Solver s = ctx.mkSolver();
  //		assertEquals(s.check(eq), Status.SATISFIABLE);
  //	}
}
