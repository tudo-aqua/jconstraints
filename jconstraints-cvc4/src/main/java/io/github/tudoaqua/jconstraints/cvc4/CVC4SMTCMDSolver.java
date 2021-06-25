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

package io.github.tudoaqua.jconstraints.cvc4;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.smtlibUtility.smtsolver.SMTCMDSolver;
import java.io.File;
import java.util.List;

public class CVC4SMTCMDSolver extends SMTCMDSolver implements UNSATCoreSolver {
  static final String UNSAT_CORE_EXTENSION = " --produce-unsat-cores";

  private File tmpFolder;

  public CVC4SMTCMDSolver() {
    super("cvc4 -L smt -m --strings-exp", false);
    smtExportConfig.replaceZ3Escape = true;
  }

  @Override
  public SolverContext createContext() {
    String cxtCommand = super.solverCommand + " --incremental";
    CVC4SMTCMDContext ctx = new CVC4SMTCMDContext(splitCMD(cxtCommand), super.smtExportConfig);
    if (super.isUnsatCoreSolver) {
      ctx.enableUnsatTracking();
    }
    return ctx;
  }

  @Override
  public void enableUnsatTracking() {
    super.solverCommand += UNSAT_CORE_EXTENSION;
    super.smtExportConfig.namedAssert = true;
    super.isUnsatCoreSolver = true;
  }

  @Override
  public List<Expression<Boolean>> getUnsatCore() {
    return super.unsatCoreLastRun;
  }
}
