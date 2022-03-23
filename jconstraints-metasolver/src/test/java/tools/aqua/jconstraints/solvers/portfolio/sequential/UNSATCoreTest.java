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

package tools.aqua.jconstraints.solvers.portfolio.sequential;

import static gov.nasa.jpf.constraints.expressions.LogicalOperator.AND;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.EQUIV;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.IMPLY;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.OR;
import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.util.Properties;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import tools.aqua.jconstraints.solvers.AbstractTest;

public class UNSATCoreTest extends AbstractTest {

  @Test
  @Disabled("We need to fix CVC4 binary provisioning first.")
  public void example1Test() {
    ConstraintSolver unsatCoreSolver = new SequentialMultiStrategySolver(new Properties());
    SolverContext ctx = unsatCoreSolver.createContext();

    Variable<Boolean> p = Variable.create(BuiltinTypes.BOOL, "p");
    Variable<Boolean> q = Variable.create(BuiltinTypes.BOOL, "q");
    Variable<Boolean> r = Variable.create(BuiltinTypes.BOOL, "r");
    Variable<Boolean> s = Variable.create(BuiltinTypes.BOOL, "s");

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
  }
}
