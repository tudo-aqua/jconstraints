/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * <p>This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * <p>Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377 the original license
 * is: Copyright (C) 2015, United States Government, as represented by the Administrator of the
 * National Aeronautics and Space Administration. All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment platform is licensed
 * under the Apache License, Version 2.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues under Apache
 * 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.smtlibUtility.solver;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import java.io.PrintStream;
import java.util.List;

public class SMTLibExportSolverContext extends SolverContext {

  private SolverContext backCtx;

  private SMTLibExportGenContext genCtx;

  private SMTLibExportVisitor visitor;

  public SMTLibExportSolverContext(SolverContext backCtx, PrintStream out) {
    this.backCtx = backCtx;
    this.genCtx = new SMTLibExportGenContext(out);
    this.visitor = new SMTLibExportVisitor(genCtx);
  }

  @Override
  public void push() {
    genCtx.push();
    backCtx.push();
  }

  @Override
  public void pop(int n) {
    backCtx.pop(n);
    genCtx.pop(n);
  }

  @Override
  public ConstraintSolver.Result solve(Valuation val) {
    genCtx.solve();
    return backCtx.solve(val);
  }

  @Override
  public void add(List<Expression<Boolean>> expressions) {
    for (Expression<?> e : expressions) {
      visitor.transform(e);
    }
    backCtx.add(expressions);
  }

  @Override
  public void dispose() {
    // nothing
  }
}