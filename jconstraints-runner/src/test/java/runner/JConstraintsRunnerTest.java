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

package runner;

import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportGenContext;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportVisitor;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportVisitorConfig;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import io.github.tudoaqua.jconstraints.cvc5.CVC5Solver;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.Properties;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import tools.aqua.jconstraints.solvers.portfolio.sequential.SequentialMultiStrategySolver;

public class JConstraintsRunnerTest {
  @Test
  public void runnerTest() throws IOException, SMTLIBParserException {
    String filenamePWD =
        "/Users/maltemues/Development/string_constraints/cleaned_benchmark/jconstraints-runner/";
    String problem = "../banditfuzz/final/3681_1565555450.7242634407178813325606425_1.smt";

    SMTProblem smtProblem = SMTLIBParser.parseSMTProgramFromFile(filenamePWD + problem);
    CVC5Solver solver = new CVC5Solver(new HashMap<>());
    SolverContext ctx = solver.createContext();
    for (Expression e : smtProblem.assertions) {
      System.out.println(e);
      ctx.add(e);
    }
    Valuation val = new Valuation();
    Result res = ctx.solve(val);
    assert res != Result.DONT_KNOW;
  }

  @Test
  public void runnerZ3Test() throws IOException, SMTLIBParserException {
    String filenamePWD =
        "/Users/maltemues/Development/string_constraints/cleaned_benchmark/jconstraints-runner/";
    String problem = "../joacosuite/JOACO/3965_OrderStatus_VxA0.smt2";

    SMTProblem smtProblem = SMTLIBParser.parseSMTProgramFromFile(filenamePWD + problem);
    NativeZ3Solver solver = new NativeZ3Solver();
    SolverContext ctx = solver.createContext();
    for (Expression e : smtProblem.assertions) {
      System.out.println(e);
      ctx.add(e);
    }
    Valuation val = new Valuation();
    Result res = ctx.solve(val);
    assert res != Result.DONT_KNOW;
  }

  @Test
  public void runner2Test() throws IOException, SMTLIBParserException {
    String filenamePWD =
        "/Users/maltemues/Development/string_constraints/cleaned_benchmark/jconstraints-runner/";
    String problem = "../nornbenchmarks/ab/4823_norn-benchmark-127.smt2";

    SMTProblem smtProblem = SMTLIBParser.parseSMTProgramFromFile(filenamePWD + problem);
    ConstraintSolver solver = new CVC5Solver();
    SolverContext ctx = solver.createContext();
    ByteArrayOutputStream baos = new ByteArrayOutputStream();
    PrintStream ps = new PrintStream(baos);

    SMTLibExportGenContext sctx = new SMTLibExportGenContext(ps);
    SMTLibExportVisitor vi =
        new SMTLibExportVisitor(sctx, new SMTLibExportVisitorConfig(false, true, true));
    for (Expression e : smtProblem.assertions) {
      System.out.println(e);
      ctx.add(e);
      vi.transform(e);
    }
    sctx.flush();
    System.out.println(baos.toString());
    Valuation val = new Valuation();
    Result res = ctx.solve(val);
    assertTrue(res != Result.DONT_KNOW && res != Result.ERROR);
    if (res.equals(Result.SAT)) {
      for (Expression<Boolean> e : smtProblem.assertions) {
        System.out.println(e);
        System.out.flush();
        assertTrue(e.evaluateSMT(val));
      }
      assertTrue(smtProblem.getAllAssertionsAsConjunction().evaluateSMT(val));
    }
  }

  @Test
  @Disabled // FIXME: Is this test broken?
  public void runner3Test() throws IOException, SMTLIBParserException {
    String filenamePWD =
        "/Users/maltemues/Development/string_constraints/cleaned_benchmark/jconstraints-runner/";
    String problem = "../nornbenchmarks/ab/4835_norn-benchmark-147.smt2";

    SMTProblem smtProblem = SMTLIBParser.parseSMTProgramFromFile(filenamePWD + problem);
    ConstraintSolver solver = new SequentialMultiStrategySolver(new Properties());
    SolverContext ctx = solver.createContext();

    for (Expression e : smtProblem.assertions) {
      System.out.println(e);
      ctx.add(e);
    }
    Valuation val = new Valuation();
    Result res = ctx.solve(val);
    assertTrue(res != Result.DONT_KNOW && res != Result.ERROR);
    if (res.equals(Result.SAT)) {
      for (Expression<Boolean> e : smtProblem.assertions) {
        assertTrue(e.evaluateSMT(val));
      }
      assertTrue(smtProblem.getAllAssertionsAsConjunction().evaluateSMT(val));
    }
  }
}
