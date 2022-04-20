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

package io.github.tudoaqua.jconstraints.cvc5;

import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.junit.jupiter.api.Test;
import org.opentest4j.TestAbortedException;

public class CVC5SolverProviderTest {

  /* We disabled this as the memory clean up during Garbage collection in CVC4 is error prune.
    In applications and other enabled tests, we rap CVC4 in its own process. Once there is a new
    Java API JNI-Library, stabilizing these tests by making the JNI-Library robust against garbage collection.
    https://github.com/CVC4/CVC4/issues/5018
  */
  @Test
  public void cvc5ServiceLoaderTest() {
    CVC5Solver solver;
    try {
      solver = (CVC5Solver) ConstraintSolverFactory.createSolver("cvc5");
    } catch (UnsatisfiedLinkError e) {
      throw new TestAbortedException("No native cvc5 support", e);
    }
    Valuation val = new Valuation();
    Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "X");
    Constant<Integer> c5 = Constant.create(BuiltinTypes.SINT32, 5);
    NumericBooleanExpression nbe = NumericBooleanExpression.create(x, EQ, c5);
    Result res = solver.solve(nbe, val);
    assertEquals(res, Result.SAT);
    assertTrue(nbe.evaluate(val));
  }
}
