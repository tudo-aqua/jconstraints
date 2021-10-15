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
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportVisitorConfig;
import java.io.BufferedReader;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeoutException;

public class SMTCMDSolver extends ConstraintSolver {

  protected String solverCommand;

  protected List<Expression<Boolean>> unsatCoreLastRun;
  protected SMTLibExportVisitorConfig smtExportConfig;
  protected boolean isUnsatCoreSolver = false;

  private SMTCMDContext defaultContext;
  protected long solverTimeOut = -1;

  public SMTCMDSolver(boolean z3Mode) {
    String prop = System.getProperty("jconstraints.cmd_solver.replace_z3encoding", "false");
    smtExportConfig =
        new SMTLibExportVisitorConfig(z3Mode, isUnsatCoreSolver, Boolean.parseBoolean(prop));
  }

  public SMTCMDSolver(String solverCommand, boolean z3Mode) {
    this(z3Mode);
    this.solverCommand = solverCommand;
    init();
  }

  public SMTCMDSolver(String solverCommand, boolean z3Mode, long timeout) {
    this(z3Mode);
    this.solverCommand = solverCommand;
    solverTimeOut = timeout;
    init();
  }

  protected void init() {
    defaultContext = (SMTCMDContext) createContext();
  }

  @Override
  public Result isSatisfiable(Expression<Boolean> f) {
    return solve(f, null);
  }

  @Override
  public Result solve(Expression<Boolean> f, Valuation result) {
    try {
      defaultContext.push();
      defaultContext.add(f);
      Result res = defaultContext.solve(result);
      unsatCoreLastRun = defaultContext.unsatCoreLastRun;
      return res;
    } finally {
      defaultContext.pop();
    }
  }

  protected void enableUnsatCores() {
    smtExportConfig.namedAssert = true;
    isUnsatCoreSolver = true;
  }

  static void getModel(
      SMTLibExportGenContext ctx,
      BufferedReader processOutput,
      List<Variable<?>> vars,
      Valuation result)
      throws ExecutionException, InterruptedException, TimeoutException {
    result.shouldConvertZ3Encoding = true;
    ctx.getModel();
    try {
      Valuation problem =
          SMTLibModelParser.parseModel(
              SolverOutputUtil.readProcessOutput(ctx, processOutput), vars);
      result.putAll(problem, true);
    } catch (SMTLIBParserException e) {
      e.printStackTrace();
    }
  }

  @Override
  public SolverContext createContext() {
    String[] cmd = splitCMD(solverCommand);
    SMTCMDContext ctx =
        solverTimeOut < 0
            ? new SMTCMDContext(cmd, smtExportConfig)
            : new SMTCMDContext(cmd, smtExportConfig, solverTimeOut);
    if (isUnsatCoreSolver) {
      ctx.enableUnsatCore();
    }
    return ctx;
  }

  protected String[] splitCMD(String in) {
    return in.split(" ");
  }
}
