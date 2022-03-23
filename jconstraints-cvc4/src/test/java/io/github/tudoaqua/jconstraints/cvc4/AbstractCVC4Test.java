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

import gov.nasa.jpf.constraints.api.SolverContext;
import org.junit.jupiter.api.BeforeEach;
import org.opentest4j.TestAbortedException;

public abstract class AbstractCVC4Test {

  protected CVC4SMTCMDSolver cvc4;
  protected SolverContext cvc4Context;
  private static boolean loadingFailed = false;

  @BeforeEach
  public void initialize() {
    if (loadingFailed || System.getProperty("os.name").toLowerCase().contains("win")) {
      throw new TestAbortedException("No native CVC4 support");
    }
    try {

      cvc4 = new CVC4SMTCMDSolver();
      cvc4Context = cvc4.createContext();
    } catch (UnsatisfiedLinkError e) {
      loadingFailed = true;
      throw new TestAbortedException("No native CVC4 support", e);
    }
  }
}
