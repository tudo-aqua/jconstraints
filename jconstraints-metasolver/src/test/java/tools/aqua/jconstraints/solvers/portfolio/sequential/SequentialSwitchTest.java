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

package tools.aqua.jconstraints.solvers.portfolio.sequential;

import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import java.io.IOException;
import java.util.Properties;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

public class SequentialSwitchTest {

  @Test
  @Disabled // As this needs a lot of time and is more for experiments.
  public void switchNoUnsatCoreCheck() throws IOException, SMTLIBParserException {
    Properties p = new Properties();
    p.put("jconstraints.multi", "disableUnsatCoreChecking=true;");
    ConstraintSolver multi = new SequentialMultiStrategySolver(p);

    String problem =
        "(declare-const __string_0 String)\n"
            + "(assert (not (bvslt (bvsub ((_ int2bv 32) (str.len __string_0)) #x00000001) #x00000000)))\n"
            + "(assert (<= 0 (str.len __string_0)))\n"
            + "(assert (bvslt (bvsub ((_ int2bv 32) (str.len __string_0)) #x00000001) ((_ int2bv 32) (str.len __string_0))))\n"
            + "(declare-const __string_1 String)\n"
            + "(assert (not (bvslt #x00000000 ((_ int2bv 32) (str.len __string_1)))))";

    SMTProblem smtProblem = SMTLIBParser.parseSMTProgram(problem);

    Valuation val = new Valuation();
    Result res1 = multi.solve(smtProblem.getAllAssertionsAsConjunction(), val);
    assertEquals(res1, Result.SAT);

    SolverContext ctx = multi.createContext();
    ctx.add(smtProblem.assertions);
    Valuation val2 = new Valuation();
    Result res2 = ctx.solve(val2);
    assertEquals(res2, Result.SAT);
  }
}
