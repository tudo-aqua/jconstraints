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

package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import java.io.IOException;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("jsmtlib")
public class BitVectorExpressionsTest {

  @Test
  public void parsingBVFunc_Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun bv0 () (_ BitVec 8)) (declare-fun bv1 () (_ BitVec 32)) (assert (= ((_ zero_extend 24) bv0) bv1))");
    final Expression<Boolean> assertStmt = problem.assertions.get(0);
    System.out.println(assertStmt);
  }

  @Test
  public void parsingBVFunc_Test2Args() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun bv0 () (_ BitVec 32)) (declare-fun bv1 () (_ BitVec 8)) (assert (= ((_ extract 7 0) bv0) bv1))");
    final Expression<Boolean> assertStmt = problem.assertions.get(0);
    System.out.println(assertStmt);
  }
}
