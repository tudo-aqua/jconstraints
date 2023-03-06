/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2023 The jConstraints Authors
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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.junit.jupiter.api.Test;

/** */
public class ContextTest {

  @Test
  public void testToString() {
    ConstraintSolver solver = ConstraintSolverFactory.createSolver("z3");

    SolverContext ctx = solver.createContext();

    Variable<Double> var_i1 = Variable.create(BuiltinTypes.DOUBLE, "i1");
    Constant<Double> const_5 = Constant.create(BuiltinTypes.DOUBLE, 0.000000052);
    Constant<Double> const_10 = Constant.create(BuiltinTypes.DOUBLE, 0.000000101);
    NumericCompound<Double> inner = NumericCompound.create(var_i1, NumericOperator.PLUS, const_5);

    NumericBooleanExpression gte =
        new NumericBooleanExpression(inner, NumericComparator.LE, const_10);

    ctx.add(gte);
    System.out.println(ctx);
  }
}
