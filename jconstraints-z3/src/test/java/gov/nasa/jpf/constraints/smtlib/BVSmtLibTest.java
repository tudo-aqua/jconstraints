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

public class BVSmtLibTest {

  @Test
  public void parsingBVFuncExtend_Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun bv0 () (_ BitVec 8)) (declare-fun bv1 () (_ BitVec 32)) (assert (= ((_"
                + " zero_extend 24) bv0) bv1))");

    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.println(expr.toString());
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    System.out.println(model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
  }

  @Test
  public void parsingBVFuncExtract_Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun bv0 () (_ BitVec 32)) (declare-fun bv1 () (_ BitVec 8)) (assert (= ((_"
                + " extract 7 0) bv0) bv1))");

    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.println(expr.toString());
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    System.out.println(model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
  }
}
