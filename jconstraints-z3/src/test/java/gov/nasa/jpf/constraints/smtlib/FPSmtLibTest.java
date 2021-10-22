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

package gov.nasa.jpf.constraints.smtlib;

import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import java.io.IOException;
import org.junit.jupiter.api.Test;

public class FPSmtLibTest {

  @Test
  public void solvingFPFunc_Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun f0 () (_ FloatingPoint 8 24)) (assert (fp.eq f0 f0))");

    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.println(expr.toString());
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    System.out.println(model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
  }

  @Test
  public void solvingFPFuncCast_Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun b0 () (_ BitVec 32)) (declare-fun f0 () (_ FloatingPoint 11 53)) (assert (= b0 ((_ fp.to_sbv 32) (RNE RoundingMode) ((_ to_fp 8 24) (RNE RoundingMode) (fp.add  (RNE RoundingMode) f0 f0)))))");

    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.println(expr.toString());
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    System.out.println(model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
  }

  @Test
  public void solvingFPFuncD2L_Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun __double_0 () (_ FloatingPoint 11 53)) (assert (bvsle ((_ fp.to_sbv 64) (RNE RoundingMode) (fp.add (RNE RoundingMode) (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000) __double_0)) #x0000000000000000)) ");

    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.println(expr.toString());
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    System.out.println(model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
  }

  @Test
  public void parsingFPLitFun_Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun __double_0 () (_ FloatingPoint 8 24))"
                + "(assert (and "
                + "(fp.eq (_ +zero 8 24)  (fp #b0 #b00000000 #b00000000000000000000000) )"
                + "(fp.eq (_ -zero 8 24)  (fp #b1 #b00000000 #b00000000000000000000000) )"
                + "(fp.isZero (_ +zero 8 24) )"
                + "(not (fp.isNaN (_ +zero 8 24) ))"
                + "(fp.isNormal __double_0 )"
                + "))");

    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.println(expr.toString());
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    System.out.println(model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
  }
}
