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

import static gov.nasa.jpf.constraints.expressions.NumericComparator.LT;
import static org.junit.jupiter.api.Assertions.*;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportGenContext;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportVisitor;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import io.github.tudoaqua.jconstraints.cvc5.AbstractCVC5Test;
import java.io.IOException;
import org.junit.jupiter.api.Test;

public class NumericTest extends AbstractCVC5Test {

  @Test
  public void firstTest() {
    Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
    Constant<Integer> c4 = Constant.create(BuiltinTypes.SINT32, 5);
    NumericBooleanExpression expr = NumericBooleanExpression.create(x, NumericComparator.LT, c4);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));

    expr = NumericBooleanExpression.create(x, NumericComparator.EQ, c4);

    val = new Valuation();
    res = cvc5.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));
  }

  @Test
  public void secondTest() {
    Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
    NumericCompound<Integer> computation1 =
        NumericCompound.create(x, NumericOperator.MUL, Constant.create(BuiltinTypes.SINT32, 2));
    computation1 =
        NumericCompound.create(
            computation1, NumericOperator.PLUS, Constant.create(BuiltinTypes.SINT32, 1));
    CastExpression<Integer, Character> casted =
        CastExpression.create(computation1, BuiltinTypes.UINT16);
    CastExpression<Character, Integer> casted2 = CastExpression.create(casted, BuiltinTypes.SINT32);
    BitvectorExpression<Integer> bvOr =
        BitvectorExpression.create(
            casted2, BitvectorOperator.OR, Constant.create(BuiltinTypes.SINT32, 2));
    BitvectorExpression<Integer> bvAnd =
        BitvectorExpression.create(
            bvOr, BitvectorOperator.AND, Constant.create(BuiltinTypes.SINT32, 3));
    NumericBooleanExpression compare =
        NumericBooleanExpression.create(
            bvAnd, NumericComparator.EQ, Constant.create(BuiltinTypes.SINT32, 3));

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(compare, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(compare.evaluate(val));
  }

  @Test
  public void misc1Test() {
    // (-((3 * (('_int0' % 10) + 0))) <= (3 * (('_int0' % 10) + 0)))
    Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "_int0");
    Expression<Integer> reminder =
        NumericCompound.create(x, NumericOperator.REM, Constant.create(BuiltinTypes.SINT32, 10));
    Expression<Integer> addition =
        NumericCompound.create(
            reminder, NumericOperator.PLUS, Constant.create(BuiltinTypes.SINT32, 0));
    Expression<Integer> multiplication =
        NumericCompound.create(
            Constant.create(BuiltinTypes.SINT32, 3), NumericOperator.MUL, addition);
    Expression<Integer> unary = UnaryMinus.create(multiplication);
    NumericBooleanExpression lt =
        NumericBooleanExpression.create(unary, NumericComparator.LE, multiplication);
    Valuation val = new Valuation();
    SMTLibExportGenContext ctx = new SMTLibExportGenContext(System.out);
    SMTLibExportVisitor visit = new SMTLibExportVisitor(ctx);
    visit.transform(lt);
    ConstraintSolver.Result res = cvc5.solve(lt, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    boolean evaluation = lt.evaluate(val);
    assertTrue(lt.evaluate(val));
  }

  @Test
  public void doubleTest() {
    Variable<Double> d = Variable.create(BuiltinTypes.DOUBLE, "x");
    Constant d0 = Constant.create(BuiltinTypes.DOUBLE, 0.0);
    Expression e = new FloatingPointBooleanExpression(FPComparator.FPGE, (Expression) d, d0);
    Expression e2 = new Negation(e);
    assertEquals(ConstraintSolver.Result.SAT, cvc5.isSatisfiable(e));
    assertEquals(ConstraintSolver.Result.SAT, cvc5.isSatisfiable(e2));
  }

  @Test
  public void doubleNotNaNTest() {
    Variable<Double> x = Variable.create(BuiltinTypes.DOUBLE, "x");
    Constant d0 = Constant.create(BuiltinTypes.DOUBLE, 0.0);
    Expression e =
        new Negation(new FloatingPointBooleanExpression(FPComparator.FPLE, (Expression) x, d0));
    Expression e2 =
        new Negation(new FloatingPointBooleanExpression(FPComparator.FP_IS_NAN, (Expression) x));
    Expression e3 =
        new Negation(
            new FloatingPointBooleanExpression(FPComparator.FP_IS_INFINITE, (Expression) x));
    Valuation val = new Valuation();
    assertEquals(ConstraintSolver.Result.SAT, cvc5.solve(ExpressionUtil.and(e3, e2, e), val));
    System.out.println(val.getValue(x));
    assertNotEquals(Double.NaN, val.getValue(x));
    assertNotEquals(Double.NEGATIVE_INFINITY, val.getValue(x));
    assertNotEquals(Double.POSITIVE_INFINITY, val.getValue(x));
  }

  @Test
  public void intToDoubleConversionTest() throws IOException, SMTLIBParserException {
    String input =
        "(declare-const __int_0 (_ BitVec 32))\n"
            + "(assert (not(bvsle __int_0  #x00000000)))\n"
            + "(assert (and (fp.gt ((_ to_fp  11 53) (RNE RoundingMode) (bvadd (bvsrem __int_0"
            + " #b00000000000000000000000000001010) #b00000000000000000000000000000001)) (fp #b0"
            + " #b00000000000 #b0000000000000000000000000000000000000000000000000000))(bvslt"
            + " __int_0 #b00000000000000000000000000000110)))";
    SMTProblem p = SMTLIBParser.parseSMTProgram(input);
    Valuation val = new Valuation();
    assertEquals(ConstraintSolver.Result.SAT, cvc5.solve(p.getAllAssertionsAsConjunction(), val));
  }

  @Test
  public void castToCharTest() {
    Variable x = Variable.create(BuiltinTypes.INTEGER, "X");
    Expression e1 = CastExpression.create(x, BuiltinTypes.SINT16);
    Expression e2 = CastExpression.create(e1, BuiltinTypes.SINT32);
    Expression e3 =
        NumericBooleanExpression.create(e2, LT, Constant.create(BuiltinTypes.SINT32, 4));
    Valuation val = new Valuation();
    assertEquals(ConstraintSolver.Result.SAT, cvc5.solve(e3, val));
  }
}
