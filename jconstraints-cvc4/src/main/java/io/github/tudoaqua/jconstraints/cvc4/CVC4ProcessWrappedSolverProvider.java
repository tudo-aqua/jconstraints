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
import gov.nasa.jpf.constraints.solvers.encapsulation.ProcessWrapperSolver;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

public class CVC4ProcessWrappedSolverProvider implements ConstraintSolverProvider {
  @Override
  public String[] getNames() {
    return new String[] {"cvc4process", "CVC4PROCESS"};
  }

  @Override
  public ConstraintSolver createSolver(Properties config) {
    Map<String, String> options = new HashMap<>();
    if (!config.containsKey("cvc4process.options")) {
    } else {
      String conf = config.getProperty("cvc4process.options").trim();
      String[] opts = conf.split(";");
      for (String o : opts) {
        o = o.trim();
        if (o.length() >= 1) {
          String[] val = o.split("=");
          options.put(val[0].trim(), val[1].trim());
        }
      }
    }
    ProcessWrapperSolver solver;

    if (options.containsKey("java")) {
      solver = new ProcessWrapperSolver("cvc4", options.get("java"));
    } else {
      solver = new ProcessWrapperSolver("cvc4");
    }
    return solver;
  }
}
