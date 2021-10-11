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

import static java.util.concurrent.TimeUnit.SECONDS;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.StoppableSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportGenContext;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportVisitor;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportVisitorConfig;
import gov.nasa.jpf.constraints.solvers.datastructures.ExpressionStack;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeoutException;

public class SMTCMDContext extends SolverContext implements StoppableSolver {
  // This timeout influences the solver side. 18000 s = 5 h
  private long timeoutSolverUtil = 18000000;

  private Process p;
  private SMTLibExportGenContext ctx;

  protected String[] command;

  protected List<Expression<Boolean>> unsatCoreLastRun;
  private Expression<Boolean> currentRun;

  private boolean unsatCoreSolver;
  private boolean hasCalledAdd;
  private BufferedReader solverOutput;

  private SMTLibExportVisitorConfig smtExportConfig;

  private List<Expression<Boolean>> lastUnsatCore;
  private Map<String, Expression> namedExpressions;
  private ExpressionStack stack;

  public SMTCMDContext(String[] cmd, SMTLibExportVisitorConfig config) {
    command = cmd;
    smtExportConfig = config;
    init();
  }

  public SMTCMDContext(String[] cmd, SMTLibExportVisitorConfig config, long timeOut) {
    this(cmd, config);
    timeoutSolverUtil = timeOut;
  }

  public SMTCMDContext(String[] cmd) {
    command = cmd;
    init();
  }

  private void init() {
    hasCalledAdd = false;
    stack = new ExpressionStack();
    if (unsatCoreSolver) {
      enableUnsatCore();
    }
    ProcessBuilder pb = new ProcessBuilder(command);
    pb.redirectErrorStream(true);
    try {
      p = pb.start();
      ctx = new SMTLibExportGenContext(new PrintStream(p.getOutputStream()));
      solverOutput = new BufferedReader(new InputStreamReader(p.getInputStream()));
    } catch (IOException e) {
      e.printStackTrace();
      throw new RuntimeException(e);
    }
  }

  @Override
  public void push() {
    ctx.push();
    stack.push();
  }

  @Override
  public void pop(int n) {
    ctx.pop(n);
    stack.pop(n);
  }

  @Override
  public Result solve(Valuation result) {
    String output = "";
    try {
      if (!hasCalledAdd) {
        System.out.println("You might want to add some expressions first");
      } else {
        ctx.flush();
        output += SolverOutputUtil.readProcessOutput(ctx, solverOutput, timeoutSolverUtil) + "\n";
      }

      ctx.solve();
      output += SolverOutputUtil.readProcessOutput(ctx, solverOutput, timeoutSolverUtil);
      return evaluateOutput(output, result);

    } catch (ExecutionException | IllegalStateException | InterruptedException e) {
      e.printStackTrace();
      System.err.println(
          "Something went wrong in the SMT solver process or solver shutdown during solving");
      System.err.println(output);
      return Result.ERROR;
    } catch (TimeoutException e) {
      System.err.println("Solver timed out: Could not read Solver Output");
      return Result.TIMEOUT;
    }
  }

  private Result evaluateOutput(String output, Valuation result)
      throws ExecutionException, InterruptedException, TimeoutException {
    Result res = Result.DONT_KNOW;
    for (String l : output.split("\n")) {
      if (!l.startsWith("<stdin>")) {
        if (l.equals("sat")) {
          res = Result.SAT;
          if (result != null) {
            List<Variable<?>> lvars = stack.getVarsInStack();
            SMTCMDSolver.getModel(ctx, solverOutput, lvars, result);
          }
        } else if (l.equals("unsat")) {
          res = Result.UNSAT;
          if (unsatCoreSolver) {
            unsatCoreLastRun = new ArrayList<>();
            unsatCoreLastRun.add(currentRun);
            ctx.getUnsatCore();
            analyzeCore(SolverOutputUtil.readProcessOutput(ctx, solverOutput));
          }
        }
      }
    }
    return res;
  }

  private void analyzeCore(String core) {
    lastUnsatCore = new LinkedList<>();
    String[] parts = core.split("\n");
    for (int i = 1; i < parts.length - 1; i++) {
      lastUnsatCore.add(namedExpressions.get(parts[i]));
    }
  }

  @Override
  public void add(List<Expression<Boolean>> expressions) {
    SMTLibExportVisitor visitor = new SMTLibExportVisitor(ctx, smtExportConfig);
    for (Expression<Boolean> expression : expressions) {
      hasCalledAdd = true;
      String name = visitor.transform(expression);
      currentRun = expression;
      if (unsatCoreSolver && smtExportConfig.namedAssert) {
        namedExpressions.put(name, expression);
      }
    }
    stack.add(expressions);
  }

  @Override
  public void dispose() {
    ctx.exit();
    init();
  }

  @Override
  public void stopSolver() {
    if (p.isAlive()) {
      p.destroy();
      try {
        p.waitFor(5, SECONDS);
      } catch (InterruptedException e) {
        e.printStackTrace();
      }
    }
  }

  protected void enableUnsatCore() {
    smtExportConfig.namedAssert = true;
    unsatCoreSolver = true;
    namedExpressions = new HashMap<>();
  }

  protected List<Expression<Boolean>> getUnsatCore() {
    return lastUnsatCore;
  }
}
