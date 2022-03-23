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

package tools.callables;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import java.util.HashMap;
import java.util.concurrent.Callable;
import structuralEquivalence.expressionVisitor.OperatorStatistics;
import tools.datastructure.UsedOperations;

public class OperatorAnalysisTask implements Callable<UsedOperations> {

  private final String file;

  public OperatorAnalysisTask(String file) {
    this.file = file;
  }

  @Override
  public UsedOperations call() {
    SMTProblem problem = null;
    try {
      problem = SMTLIBParser.parseSMTProgramFromFile(file);
      OperatorStatistics visitor = new OperatorStatistics();
      HashMap<String, Integer> data = new HashMap<>();
      problem.assertions.forEach(
          a -> {
            int asserts = data.getOrDefault("assert", 0);
            asserts++;
            data.put("assert", asserts);
            a.accept(visitor, data);
          });
      data.put("variable", problem.variables.size());
      return new UsedOperations(file, data);
    } catch (Exception e) {
      System.out.println(
          "Problem parsing: "
              + file
              + " "
              + (e.getMessage() == null ? e.toString() : e.getMessage()));
    }
    return null;
  }
}
