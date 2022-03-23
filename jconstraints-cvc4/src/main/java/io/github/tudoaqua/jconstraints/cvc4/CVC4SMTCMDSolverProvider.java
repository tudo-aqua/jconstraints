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

package io.github.tudoaqua.jconstraints.cvc4;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider;
import java.util.Properties;

public class CVC4SMTCMDSolverProvider implements ConstraintSolverProvider {
  @Override
  public String[] getNames() {
    return new String[] {"cvc4cmd", "CVC4CMD"};
  }

  @Override
  public ConstraintSolver createSolver(Properties config) {
    return new CVC4SMTCMDSolver();
  }
}
