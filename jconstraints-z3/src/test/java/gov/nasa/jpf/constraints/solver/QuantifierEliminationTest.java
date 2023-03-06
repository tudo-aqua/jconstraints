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

package gov.nasa.jpf.constraints.solver;

import static org.junit.jupiter.api.Assertions.assertNotNull;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;
import org.junit.jupiter.api.Test;

public class QuantifierEliminationTest {

  public QuantifierEliminationTest() {}

  @Test
  public void eliminationTest() throws IOException {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    NativeZ3Solver solver = (NativeZ3Solver) ConstraintSolverFactory.createSolver("Z3", conf);

    Variable<BigInteger> x = new Variable<>(BuiltinTypes.INTEGER, "x");
    Variable<BigInteger> a = new Variable<>(BuiltinTypes.INTEGER, "a");
    Variable<BigInteger> b = new Variable<>(BuiltinTypes.INTEGER, "b");

    Constant<BigInteger> zero = new Constant<>(BuiltinTypes.INTEGER, BigInteger.ZERO);

    // Expression expr = new NumericBooleanExpression(x, NumericComparator.EQ, x);

    Expression<Boolean> expr =
        new NumericBooleanExpression(
            x, NumericComparator.EQ, new NumericCompound<>(a, NumericOperator.PLUS, b));

    expr =
        ExpressionUtil.and(
            expr,
            new NumericBooleanExpression(a, NumericComparator.GT, zero),
            new NumericBooleanExpression(b, NumericComparator.GT, zero));

    List<Variable<?>> bound = new ArrayList<>();
    bound.add(a);
    bound.add(b);

    QuantifierExpression qe = new QuantifierExpression(Quantifier.EXISTS, bound, expr);
    System.out.println("gov.nasa.jpf.constraints.api.QuantifierEliminationTest.eliminationTest()");
    StringBuilder aa = new StringBuilder();
    qe.print(aa);
    System.out.println(aa);
    assertNotNull(solver.eliminateQuantifiers(qe));
  }
}
