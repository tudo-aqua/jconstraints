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

package io.github.tudoaqua.jconstraints.cvc4.solver;

import static gov.nasa.jpf.constraints.expressions.LogicalOperator.AND;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.EQUIV;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.IMPLY;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.OR;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import io.github.tudoaqua.jconstraints.cvc4.AbstractCVC4Test;
import io.github.tudoaqua.jconstraints.cvc4.CVC4SMTCMDSolver;
import io.github.tudoaqua.jconstraints.cvc4.CVC4Solver;
import java.util.HashMap;
import java.util.List;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

public class UNSATCoreTest extends AbstractCVC4Test {

  @Test
  public void example1Test() {
    UNSATCoreSolver cvc4UnsatCore = (UNSATCoreSolver) cvc4;
    cvc4UnsatCore.enableUnsatTracking();
    SolverContext ctx = cvc4.createContext();

    Variable p = Variable.create(BuiltinTypes.BOOL, "p");
    Variable q = Variable.create(BuiltinTypes.BOOL, "q");
    Variable r = Variable.create(BuiltinTypes.BOOL, "r");
    Variable s = Variable.create(BuiltinTypes.BOOL, "s");

    PropositionalCompound pc2 = PropositionalCompound.create(r, IMPLY, s);
    PropositionalCompound pc3 =
        PropositionalCompound.create(s, IMPLY, PropositionalCompound.create(q, EQUIV, r));
    ctx.add(PropositionalCompound.create(p, OR, q));
    ctx.add(pc2);
    ctx.add(pc3);
    ctx.add(PropositionalCompound.create(r, OR, p));
    ctx.add(PropositionalCompound.create(r, OR, s));
    ctx.add(Negation.create(PropositionalCompound.create(r, AND, q)));
    ctx.add(Negation.create(PropositionalCompound.create(s, AND, p)));
    assertEquals(Result.UNSAT, ctx.solve(null));
    UNSATCoreSolver unsatCTX = (UNSATCoreSolver) ctx;

    List<Expression<Boolean>> unsatCore = unsatCTX.getUnsatCore();
    assertEquals(6, unsatCore.size());
    assertTrue(unsatCore.contains(pc2));
    assertFalse(unsatCore.contains(pc3));
  }

  @Test
  public void example2Test() {
    ConstraintSolver cvc4 = new CVC4Solver(new HashMap<>());
    UNSATCoreSolver cvc4UnsatCore = (UNSATCoreSolver) cvc4;
    cvc4UnsatCore.enableUnsatTracking();
    SolverContext ctx = cvc4.createContext();
    ctx.push();
    ctx.pop();
    ctx.push();

    Variable p = Variable.create(BuiltinTypes.BOOL, "p");
    Variable q = Variable.create(BuiltinTypes.BOOL, "q");
    Variable r = Variable.create(BuiltinTypes.BOOL, "r");
    Variable s = Variable.create(BuiltinTypes.BOOL, "s");

    PropositionalCompound pc2 = PropositionalCompound.create(r, IMPLY, s);
    PropositionalCompound pc3 =
        PropositionalCompound.create(s, IMPLY, PropositionalCompound.create(q, EQUIV, r));
    ctx.add(PropositionalCompound.create(p, OR, q));
    ctx.add(pc2);
    ctx.add(pc3);
    ctx.add(PropositionalCompound.create(r, OR, p));
    ctx.add(PropositionalCompound.create(r, OR, s));
    ctx.add(Negation.create(PropositionalCompound.create(r, AND, q)));
    ctx.add(Negation.create(PropositionalCompound.create(s, AND, p)));
    assertEquals(Result.UNSAT, ctx.solve(null));
    UNSATCoreSolver unsatCTX = (UNSATCoreSolver) ctx;

    List<Expression<Boolean>> unsatCore = unsatCTX.getUnsatCore();
    assertEquals(6, unsatCore.size());
    assertTrue(unsatCore.contains(pc2));
    assertFalse(unsatCore.contains(pc3));
  }

  @Test
  @Disabled("Cannot be run without CVC4 binary on path at the moment")
  public void example3Test() {
    ConstraintSolver cvc4 = new CVC4SMTCMDSolver();
    UNSATCoreSolver cvc4UnsatCore = (UNSATCoreSolver) cvc4;
    cvc4UnsatCore.enableUnsatTracking();
    SolverContext ctx = cvc4.createContext();
    Variable p = Variable.create(BuiltinTypes.BOOL, "p");
    Variable q = Variable.create(BuiltinTypes.BOOL, "q");
    Variable r = Variable.create(BuiltinTypes.BOOL, "r");
    Variable s = Variable.create(BuiltinTypes.BOOL, "s");

    PropositionalCompound pc2 = PropositionalCompound.create(r, IMPLY, s);
    PropositionalCompound pc3 =
        PropositionalCompound.create(s, IMPLY, PropositionalCompound.create(q, EQUIV, r));
    ctx.add(PropositionalCompound.create(p, OR, q));
    ctx.add(pc2);
    ctx.add(pc3);
    ctx.add(PropositionalCompound.create(r, OR, p));
    ctx.add(PropositionalCompound.create(r, OR, s));
    ctx.add(Negation.create(PropositionalCompound.create(r, AND, q)));
    ctx.add(Negation.create(PropositionalCompound.create(s, AND, p)));
    assertEquals(Result.UNSAT, ctx.solve(null));
    UNSATCoreSolver unsatCTX = (UNSATCoreSolver) ctx;

    List<Expression<Boolean>> unsatCore = unsatCTX.getUnsatCore();
    assertEquals(6, unsatCore.size());
    assertTrue(unsatCore.contains(pc2));
    assertFalse(unsatCore.contains(pc3));
  }
}
