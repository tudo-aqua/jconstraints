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

package io.github.tudoaqua.jconstraints.cvc5.serialization;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import io.github.tudoaqua.jconstraints.cvc4.CVC4Solver;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.util.HashMap;
import java.util.LinkedList;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

public class SerializationDebuggingTest {

  @Test
  @Disabled
  public void test() throws IOException, ClassNotFoundException {
    FileInputStream fis = new FileInputStream("/tmp/serialized_cvc4239418837829521");
    ObjectInputStream ois = new ObjectInputStream(fis);
    Object o = ois.readObject();
    CVC4Solver cvc4 = new CVC4Solver(new HashMap<>());
    SolverContext ctx = cvc4.createContext();
    for (Expression e : (LinkedList<Expression>) o) {
      System.out.println("Adding: ");
      System.out.println(e.toString());
      e = ExpressionUtil.and(ExpressionUtil.TRUE, e);
      ctx.add(e);
    }
    Valuation val = new Valuation();
    Result res = ctx.solve(val);
    assert res != Result.DONT_KNOW;
  }
}
