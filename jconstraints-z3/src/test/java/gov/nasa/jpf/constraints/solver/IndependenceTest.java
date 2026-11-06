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

package gov.nasa.jpf.constraints.solver;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import java.util.Properties;
import org.junit.jupiter.api.Test;

/** Solving independent groups of constraints separately (z3.independence). */
public class IndependenceTest {

  private static SolverContext context() {
    Properties p = new Properties();
    p.setProperty("symbolic.dp", "z3");
    p.setProperty("z3.timeout", "10000");
    ConstraintSolver solver = ConstraintSolverFactory.createSolver("z3", p);
    return solver.createContext();
  }

  private static void add(SolverContext ctx, String smt) throws Exception {
    ctx.push();
    SMTLIBParser.parseSMTProgram(smt).addProblemToContext(ctx);
  }

  /**
   * After a push and with an unrelated integer constraint, Z3 5 does not decide fp.sqrt within 10 s
   * (it solves the floating-point constraint with the general SMT core); separately, it is solved
   * by bit-blasting in well under a second.
   */
  @Test
  public void fpNextToUnrelatedInteger() throws Exception {
    SolverContext ctx = context();
    add(ctx, "(declare-fun null () Int)(assert (= null 0))");
    add(
        ctx,
        "(declare-fun d () (_ FloatingPoint 11 53))"
            + "(assert (fp.eq (fp.sqrt RNE d) ((_ to_fp 11 53) RNE 3.0)))");
    Valuation val = new Valuation();
    assertEquals(Result.SAT, ctx.solve(val));
    assertEquals(9.0, (Double) val.getValue("d"));
    assertEquals(0, ((Number) val.getValue("null")).intValue());
  }

  /** a group is UNSAT: the conjunction is UNSAT */
  @Test
  public void unsatGroup() throws Exception {
    SolverContext ctx = context();
    add(ctx, "(declare-fun x () Int)(assert (> x 3))");
    add(ctx, "(declare-fun y () Int)(assert (and (> y 3) (< y 2)))");
    assertEquals(Result.UNSAT, ctx.solve(new Valuation()));
    ctx.pop();
    assertEquals(Result.SAT, ctx.solve(new Valuation()));
  }

  /**
   * groups connected through a shared variable are solved together; the model satisfies all
   * constraints
   */
  @Test
  public void connectedGroups() throws Exception {
    String smt =
        "(declare-fun x () Int)(declare-fun y () Int)(declare-fun z () Int)(declare-fun s ()"
            + " String)(assert (> x 3))(assert (= y (+ x 1)))(assert (< z 0))(assert (= (str.len s)"
            + " y))";
    SMTProblem problem = SMTLIBParser.parseSMTProgram(smt);
    SolverContext ctx = context();
    ctx.add(problem.getAllAssertionsAsConjunction());
    Valuation val = new Valuation();
    assertEquals(Result.SAT, ctx.solve(val));
    assertTrue(problem.getAllAssertionsAsConjunction().evaluate(val));
  }

  /**
   * integer and bit-vector groups are solved after a push (incremental SMT core): without it, Z3 5
   * returns N = 2^30 for N > 1, and programs that allocate an array of size N run out of memory
   */
  @Test
  public void smallBitVectorModel() throws Exception {
    SolverContext ctx = context();
    add(
        ctx,
        "(declare-fun d () (_ FloatingPoint 11 53))"
            + "(assert (fp.gt d ((_ to_fp 11 53) RNE 1.0)))");
    add(
        ctx,
        "(declare-fun n () (_ BitVec 32))(assert (bvsgt n #x00000000))"
            + "(assert (not (bvsle n #x00000001)))");
    Valuation val = new Valuation();
    assertEquals(Result.SAT, ctx.solve(val));
    int n = ((Number) val.getValue("n")).intValue();
    assertTrue(n > 1 && n < 1000, "n = " + n);
  }
}
