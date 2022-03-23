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

package gov.nasa.jpf.constraints.smtlibUtility;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.smtlibUtility.smtsolver.SMTCMDSolver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("manual")
public class CMDSolverTest {
  @Test
  public void runSMTCMDSolverIsSatisfiableTest() throws IOException {
    ConstraintSolver cs = new SMTCMDSolver("cvc4 -L smt --strings-exp", false);
    Variable<Integer> v = Variable.create(BuiltinTypes.SINT32, "x");
    NumericBooleanExpression nbe =
        NumericBooleanExpression.create(
            v, NumericComparator.GT, Constant.create(BuiltinTypes.SINT32, 5));
    assertEquals(Result.SAT, cs.isSatisfiable(nbe));
  }

  @Test
  public void runSMTCMDSolverSolveTest() throws IOException {
    ConstraintSolver cs = new SMTCMDSolver("cvc4 -L smt -m --strings-exp", false);
    Variable<Integer> v = Variable.create(BuiltinTypes.SINT32, "x");
    NumericBooleanExpression nbe =
        NumericBooleanExpression.create(
            v, NumericComparator.GT, Constant.create(BuiltinTypes.SINT32, 5));
    Valuation val = new Valuation();
    assertEquals(Result.SAT, cs.solve(nbe, val));
    assertTrue(nbe.evaluate(val));
  }

  @Test
  public void runSMTCMDContextSolveTest() {
    ConstraintSolver cs = new SMTCMDSolver("cvc4 -L smt -m --strings-exp", false);
    SolverContext ctx = cs.createContext();
    Variable<Integer> v = Variable.create(BuiltinTypes.SINT32, "x");
    NumericBooleanExpression nbe =
        NumericBooleanExpression.create(
            v, NumericComparator.GT, Constant.create(BuiltinTypes.SINT32, 5));
    ctx.add(nbe);
    Valuation val = new Valuation();
    assertEquals(Result.SAT, ctx.solve(val));
    assertTrue(nbe.evaluate(val));
  }

  @Test
  public void runSMTCMDContextSolve2Test() {
    ConstraintSolver cs = new SMTCMDSolver("cvc4 -L smt -m --strings-exp", false);
    SolverContext ctx = cs.createContext();
    Variable<Integer> v = Variable.create(BuiltinTypes.SINT32, "x");
    NumericBooleanExpression nbe =
        NumericBooleanExpression.create(
            v, NumericComparator.GT, Constant.create(BuiltinTypes.SINT32, -3));
    ctx.add(nbe);
    Valuation val = new Valuation();
    assertEquals(Result.SAT, ctx.solve(val));
    assertTrue(nbe.evaluate(val));
  }
}
