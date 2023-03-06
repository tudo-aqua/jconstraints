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

package structuralEquivalence.expressionVisitor;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import java.io.File;
import java.util.HashMap;
import org.junit.jupiter.api.Test;
import structuralEquivalence.Processor;

public class OperatorStatisticsTestQFLIATest {

  @Test
  public void parsing100_correcstr_readable_smt2Test() {
    SMTProblem problem =
        Processor.parseFile(
            new File(
                this.getClass().getClassLoader().getResource("QF_LIA/prp-0-14.smt2").getFile()));
    OperatorStatistics visitor = new OperatorStatistics();
    HashMap<String, Integer> data = new HashMap<>();
    problem.getAllAssertionsAsConjunction().accept(visitor, data);
    assertFalse(data.isEmpty());
    assertTrue(data.containsKey("let"));
    assertTrue(data.containsKey("ite"));
    assertTrue(data.containsKey("<="));
    assertTrue(data.containsKey("+"));
    assertTrue(data.containsKey("=="));
  }
}
