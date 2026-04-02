/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2026 The jConstraints Authors
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

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import java.io.IOException;
import java.util.Properties;
import org.junit.jupiter.api.Test;

public class FunctionTest {

  @Test
  public void testFunctionDefinition() throws IOException, SMTLIBParserException {
    SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun __object_0.cls () String)\n"
                + "\n"
                + "(assert (or\n"
                + "  (= __object_0.cls \"LA;\")\n"
                + "  (= __object_0.cls \"LB;\")\n"
                + "  (= __object_0.cls \"LC;\")\n"
                + "))\n"
                + "\n"
                + "(declare-fun obj.extends (String String) Bool)\n"
                + "(assert (forall ((sub String) (sup String))\n"
                + "  (= (obj.extends sub sup)  \n"
                + "  (ite (or    \n"
                + "    (and (= sub \"null\") (= sup \"LA;\"))\n"
                + "    (and (= sub \"null\") (= sup \"LB;\"))\n"
                + "    (and (= sub \"null\") (= sup \"LC;\"))\n"
                + "    (and (= sub \"null\") (= sup \"Ltest/D;\"))\n"
                + "    (and (= sub \"LA;\")  (= sup \"LA;\"))\n"
                + "    (and (= sub \"LB;\")  (= sup \"LB;\"))\n"
                + "    (and (= sub \"LB;\")  (= sup \"LA;\"))\n"
                + "    (and (= sub \"LC;\")  (= sup \"LC;\"))\n"
                + "    (and (= sub \"LC;\")  (= sup \"LB;\"))\n"
                + "    (and (= sub \"LC;\")  (= sup \"LA;\"))\n"
                + "    (and (= sub \"Ltest/D;\") (= sup \"Ltest/D;\"))    \n"
                + "  ) true false)\n"
                + ")))\n"
                + "\n"
                + "(assert (not (obj.extends __object_0.cls \"LC;\"))) \n"
                + "\n"
                + "(check-sat)\n"
                + "(get-model)");
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    ConstraintSolver solver = ConstraintSolverFactory.createSolver("z3", conf);
    Valuation val = new Valuation();
    ConstraintSolver.Result result = solver.solve(problem.getAllAssertionsAsConjunction(), val);
    System.out.println("Result: " + result);
    System.out.println("Valuation: " + val);
  }
}
