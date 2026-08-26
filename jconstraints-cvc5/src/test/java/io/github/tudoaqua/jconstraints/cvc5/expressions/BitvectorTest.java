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

package io.github.tudoaqua.jconstraints.cvc5.expressions;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import io.github.tudoaqua.jconstraints.cvc5.AbstractCVC5Test;
import java.io.IOException;
import org.junit.jupiter.api.Test;

public class BitvectorTest extends AbstractCVC5Test {

  @Test
  public void testBitvectorAbs() throws IOException {
    Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
    Constant<Integer> c4 = Constant.create(BuiltinTypes.SINT32, -5);

    Expression expr = NumericBooleanExpression.create(x, NumericComparator.EQ, c4);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue((boolean) expr.evaluate(val));

    System.out.println(val);

    Expression expr2 =
        BitvectorExpression.create(
            x, BitvectorOperator.SHIFTR, Constant.create(BuiltinTypes.SINT32, 31));
    Expression expr3 = NumericCompound.create(expr2, NumericOperator.PLUS, x);
    Expression expr4 = BitvectorExpression.create(expr3, BitvectorOperator.OR, expr2);
    Expression expr5 =
        NumericBooleanExpression.create(
            expr4, NumericComparator.EQ, Constant.create(BuiltinTypes.SINT32, 5));
    expr5.print(System.out);
    System.out.println();

    val = new Valuation();
    res = cvc5.solve(expr5, val);
    System.out.println(val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    // assertTrue((boolean) expr5.evaluate(val));
  }

  @Test
  public void testShortConst() {
    Variable<Short> x = Variable.create(BuiltinTypes.SINT16, "x");
    Constant<Short> c4 = Constant.create(BuiltinTypes.SINT16, (short) 5);

    Expression expr = NumericBooleanExpression.create(x, NumericComparator.EQ, c4);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc5.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue((boolean) expr.evaluate(val));
  }
}
