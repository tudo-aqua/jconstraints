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

package tools.aqua.jconstraints.solvers.portfolio.sequential;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider;
import java.util.Properties;

public class SequentialMultiStrategySolverProvider implements ConstraintSolverProvider {

  @Override
  public String[] getNames() {
    return new String[] {"sequentialPortfolio", "multi"};
  }

  @Override
  public ConstraintSolver createSolver(Properties properties) {
    SequentialMultiStrategySolver smss = new SequentialMultiStrategySolver(properties);
    String options_encoded = properties.getProperty("jconstraints.multi");
    if (options_encoded != null) {
      String[] options = options_encoded.replace("\"", "").split(";");
      for (String s : options) {
        String[] key_value = s.split("=");
        if (key_value[0].equalsIgnoreCase("disableUnsatCoreChecking")
            && key_value[1].equals("true")) {
          smss.disableUNSATCoreChecking();
        }
      }
    }
    return smss;
  }
}
