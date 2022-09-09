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

package io.github.tudoaqua.jconstraints.benchmarkTest;

import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import java.util.Properties;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.params.ParameterizedTest;
import tools.aqua.jconstraints.benchmarktest.api.TestCaseSource;
import tools.aqua.jconstraints.benchmarktest.benchmarks.SINT32ConstantTestExpressions;
import tools.aqua.jconstraints.benchmarktest.benchmarks.SINT32VariableTestExpressions;
import tools.aqua.jconstraints.benchmarktest.benchmarks.SINT64ConstantTestExpressions;
import tools.aqua.jconstraints.benchmarktest.benchmarks.StringConstantTestExpressions;
import tools.aqua.jconstraints.benchmarktest.benchmarks.TestCase;
import tools.aqua.jconstraints.solvers.portfolio.sequential.SequentialMultiStrategySolverProvider;

public class MultiBenchmark {
  private static SequentialMultiStrategySolverProvider provider;
  private static ConstraintSolver solver;

  @BeforeAll
  public static void init() {
    provider = new SequentialMultiStrategySolverProvider();
    solver = provider.createSolver(new Properties());
  }

  @ParameterizedTest
  @TestCaseSource({
    SINT32ConstantTestExpressions.class,
    SINT64ConstantTestExpressions.class,
    SINT32VariableTestExpressions.class,
    StringConstantTestExpressions.class
  })
  public void testAll(TestCase test) {
    assertEquals(test.getExpectedResult(), solver.isSatisfiable(test.getTest()));
  }
}
