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

package structuralEquivalence;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import java.io.File;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class ProcessorTest {

  SMTProblem problem1, problem2, problem3, problem4, p5, p6, p7, p8;

  @BeforeEach
  public void setup() {
    problem1 =
        Processor.parseFile(
            new File(
                this.getClass()
                    .getClassLoader()
                    .getResource("100.corecstrs.readable.smt2")
                    .getFile()));
    problem2 =
        Processor.parseFile(
            new File(
                this.getClass()
                    .getClassLoader()
                    .getResource("101.corecstrs.readable.smt2")
                    .getFile()));
    problem3 =
        Processor.parseFile(
            new File(
                this.getClass()
                    .getClassLoader()
                    .getResource("103.corecstrs.readable.smt2")
                    .getFile()));
    problem4 =
        Processor.parseFile(
            new File(
                this.getClass()
                    .getClassLoader()
                    .getResource("110.corecstrs.readable.smt2")
                    .getFile()));
    p5 =
        Processor.parseFile(
            new File(this.getClass().getClassLoader().getResource("concat-036.smt2").getFile()));
    p6 =
        Processor.parseFile(
            new File(this.getClass().getClassLoader().getResource("concat-037.smt2").getFile()));
    p7 =
        Processor.parseFile(
            new File(this.getClass().getClassLoader().getResource("endswith-004.smt2").getFile()));
    p8 =
        Processor.parseFile(
            new File(
                this.getClass().getClassLoader().getResource("startswith-004.smt2").getFile()));
  }

  @Test
  public void p1Andp3EqualsTest() {
    boolean res = Processor.compareProblems(problem1, problem3);
    assertTrue(res);
  }

  @Test
  public void p1Andp2EqualsTest() {
    assertTrue(Processor.compareProblems(problem1, problem2));
  }

  @Test
  public void p1Andp4NotEqualsTest() {
    assertFalse(Processor.compareProblems(problem1, problem4));
  }

  @Test
  public void p5Andp6NotEqualsTest() {
    assertFalse(Processor.compareProblems(p5, p6));
  }

  @Test
  public void p7Andp8NotEqualsTest() {
    assertFalse(Processor.compareProblems(p7, p8));
  }
}
