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

package gov.nasa.jpf.constraints.smtlibUtility.smtsolver;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLibModelParser;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportGenContext;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportVisitor;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportVisitorConfig;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.TimeUnit;

public class SMTCMDSolver extends ConstraintSolver {

  protected String solverCommand;

  protected List<Expression<Boolean>> unsatCoreLastRun = null;
  protected SMTLibExportVisitorConfig smtExportConfig;
  protected boolean isUnsatCoreSolver = false;

  public SMTCMDSolver(String solverCommand, boolean z3Mode) {
    this.solverCommand = solverCommand;
    String prop = System.getProperty("jconstraints.cmd_solver.replace_z3encoding", "false");
    smtExportConfig =
        new SMTLibExportVisitorConfig(z3Mode, isUnsatCoreSolver, Boolean.parseBoolean(prop));
  }

  @Override
  public Result isSatisfiable(Expression<Boolean> f) {
    return solveInProcess(f, null);
  }

  @Override
  public Result solve(Expression<Boolean> f, Valuation result) {
    return solveInProcess(f, result);
  }

  private Result solveInProcess(Expression<Boolean> f, Valuation result) {
    try {
      ProcessBuilder pb = new ProcessBuilder(splitCMD(solverCommand));
      pb.redirectErrorStream(true);
      Process p = pb.start();
      try (PrintStream ps = new PrintStream(p.getOutputStream(), true);
          BufferedReader bos = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
        SMTLibExportGenContext ctx = new SMTLibExportGenContext(ps);
        SMTLibExportVisitor visitor = new SMTLibExportVisitor(ctx, smtExportConfig);
        visitor.transform(f);
        String output = "";
        String line;
        while (!bos.ready() && p.isAlive()) {
          Thread.sleep(10);
        }
        while (bos.ready() && (line = bos.readLine()) != null) {
          output += line;
          output += "\n";
        }
        unsatCoreLastRun = null;
        ctx.solve();
        String solving = "";
        while (!bos.ready() && p.isAlive()) {
          Thread.sleep(10);
        }
        while (bos.ready() && (line = bos.readLine()) != null) {
          output += line;
          output += "\n";
        }
        Result res = Result.DONT_KNOW;
        for (String l : output.split("\n")) {
          if (l.startsWith("<stdin>")) {
            continue;
          } else {
            if (l.equals("sat")) {
              res = Result.SAT;
              if (result != null) {
                List<Variable<?>> vars = new LinkedList<>(ExpressionUtil.freeVariables(f));
                getModel(ctx, bos, vars, result);
              }
            } else if (l.equals("unsat")) {
              res = Result.UNSAT;
              if (isUnsatCoreSolver) {
                unsatCoreLastRun = new ArrayList<>();
                unsatCoreLastRun.add(f);
              }
            }
          }
        }
        ctx.exit();
        p.waitFor(500, TimeUnit.MILLISECONDS);
        return res;
      }
    } catch (IOException | InterruptedException e) {
      e.printStackTrace();
    }
    return Result.ERROR;
  }

  protected void enableUnsatCores() {
    smtExportConfig.namedAssert = true;
    isUnsatCoreSolver = true;
  }

  static void getModel(
      SMTLibExportGenContext ctx, BufferedReader bos, List<Variable<?>> vars, Valuation result)
      throws IOException, InterruptedException {
    result.shouldConvertZ3Encoding = true;
    ctx.getModel();
    while (!bos.ready()) {
      Thread.sleep(10);
    }
    String model = "", line;
    while (bos.ready() && (line = bos.readLine()) != null) {
      model += line;
      model += "\n";
    }
    try {
      Valuation problem = SMTLibModelParser.parseModel(model, vars);
      result.putAll(problem, true);
    } catch (SMTLIBParserException e) {
      e.printStackTrace();
    }
  }

  @Override
  public SolverContext createContext() {
    SMTCMDContext ctx = new SMTCMDContext(splitCMD(solverCommand), smtExportConfig);
    if (isUnsatCoreSolver) {
      ctx.enableUnsatCore();
    }
    return ctx;
  }

  protected String[] splitCMD(String in) {
    return in.split(" ");
  }
}
