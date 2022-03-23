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

package gov.nasa.jpf.constraints.smtComp;

import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.SAT;
import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import java.io.IOException;
import org.junit.jupiter.api.Test;

public class QF_NRA_TEST {
  @Test
  public void runGen09Test() throws SMTLIBParserException, IOException {

    final SMTProblem problem = ResourceParsingHelper.parseResourceFile("test_inputs/gen-09.smt2");
    final NativeZ3Solver solver = new NativeZ3Solver();
    final Valuation val = new Valuation();
    final ConstraintSolver.Result res = solver.solve(problem.getAllAssertionsAsConjunction(), val);
    assertEquals(res, SAT);
    assertEquals(val.getVariables().size(), 2);
  }
}
