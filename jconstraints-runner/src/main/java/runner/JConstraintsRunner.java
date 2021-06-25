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

package runner;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.exceptions.UndecidedBooleanExeception;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.encapsulation.ProcessWrapperSolver;
import io.github.tudoaqua.jconstraints.cvc4.CVC4SMTCMDSolver;
import java.io.File;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import structuralEquivalence.Processor;

public class JConstraintsRunner {

  public static void main(String args[]) {
    CommandLineParser parser = new DefaultParser();
    try {
      CommandLine cmd = parser.parse(setupOptions(), args);
      (new JConstraintsRunner()).runProgram(cmd);
    } catch (ParseException e) {
      e.printStackTrace();
    }
  }

  private void runProgram(CommandLine cmd) {
    String filepath = cmd.getOptionValue("smt");
    String solver = cmd.getOptionValue("s");
    if (solver.equalsIgnoreCase("z3")
        || solver.equalsIgnoreCase("cvc4")
        || solver.equalsIgnoreCase("multi")
        || solver.equalsIgnoreCase("cvc4cmd")) {
      ConstraintSolver constraintSolver;
      if (solver.equalsIgnoreCase("cvc4")) {
        constraintSolver = new ProcessWrapperSolver("cvc4");
      } else if (solver.equalsIgnoreCase("cvc4cmd")) {
        constraintSolver = new CVC4SMTCMDSolver();
      } else {
        constraintSolver = ConstraintSolverFactory.createSolver(solver);
      }
      SMTProblem problem = Processor.parseFile(new File(filepath));
      SolverContext ctx = constraintSolver.createContext();
      Valuation val = new Valuation();
      ctx.add(problem.assertions);
      ConstraintSolver.Result res = ctx.solve(val);
      System.out.println("RESULT: " + res);
      if (res == ConstraintSolver.Result.SAT) {
        boolean evaluated = false;
        try {
          System.out.println("Valuation: " + val.toString());
          evaluated = problem.getAllAssertionsAsConjunction().evaluateSMT(val);
        } catch (UndecidedBooleanExeception e) {
          evaluated = true;
        } catch (Throwable t) {
          t.printStackTrace();
          System.out.println("VALUATIONERROR");
        }
        System.out.println("EVALUATED: " + evaluated);
      }
    }
    System.exit(0);
  }

  private static Options setupOptions() {

    Option smtRootFolder = Option.builder("smt").longOpt("smt_file").hasArg().required().build();
    Option solver = Option.builder("s").longOpt("solver").hasArg().required().build();

    Options checkerOptions = new Options();

    checkerOptions.addOption(smtRootFolder);
    checkerOptions.addOption(solver);
    return checkerOptions;
  }
}
