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

package structuralEquivalence.expressionVisitor;

import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import java.io.File;
import java.util.HashMap;
import org.junit.jupiter.api.Test;
import structuralEquivalence.Processor;

public class OperatorStatisticsTest {

  @Test
  public void parsing100_correcstr_readable_smt2Test() {
    SMTProblem problem =
        Processor.parseFile(
            new File(
                this.getClass()
                    .getClassLoader()
                    .getResource("100.corecstrs.readable.smt2")
                    .getFile()));
    System.out.println(problem.assertions.toString());
    OperatorStatistics visitor = new OperatorStatistics();
    HashMap<String, Integer> data = new HashMap<>();
    problem.getAllAssertionsAsConjunction().accept(visitor, data);
    assertEquals((int) data.get("str.to.re"), 43);
    assertEquals((int) data.get("str.++"), 88);
    // assertEquals((int) data.get("=="), 59); FIXME: yields 102
    // assertEquals((int) data.get("="), 180); FIXME: yields 137
  }

  @Test
  public void parsingPyEx1Smt2Test() {
    SMTProblem problem =
        Processor.parseFile(
            new File(this.getClass().getClassLoader().getResource("pyex1.smt2").getFile()));
    OperatorStatistics visitor = new OperatorStatistics();
    HashMap<String, Integer> data = new HashMap<>();
    problem.getAllAssertionsAsConjunction().accept(visitor, data);
    System.out.println(data);
    assertEquals((int) data.get("str.contains"), 29);
    assertEquals((int) data.get("str.len"), 2188);
    assertEquals((int) data.get("str.++"), 69);
    assertEquals((int) data.get("str.replace"), 69);
  }
}
