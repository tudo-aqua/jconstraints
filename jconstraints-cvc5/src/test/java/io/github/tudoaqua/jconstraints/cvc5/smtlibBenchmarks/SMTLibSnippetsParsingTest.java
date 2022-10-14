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

package io.github.tudoaqua.jconstraints.cvc5.smtlibBenchmarks;

import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.SAT;
import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import io.github.tudoaqua.jconstraints.cvc5.AbstractCVC5Test;
import java.io.IOException;
import org.junit.jupiter.api.Test;

public class SMTLibSnippetsParsingTest extends AbstractCVC5Test {

  @Test
  public void testUsedInMulti() throws IOException, SMTLIBParserException {
    String problem =
        "(declare-const __string_0 String)\n"
            + "(assert (not (bvslt (bvsub ((_ int2bv 32) (str.len __string_0)) #x00000001) #x00000000)))\n"
            + "(assert (<= 0 (str.len __string_0)))\n"
            + "(assert (bvslt (bvsub ((_ int2bv 32) (str.len __string_0)) #x00000001) ((_ int2bv 32) (str.len __string_0))))\n"
            + "(declare-const __string_1 String)\n"
            + "(assert (not (bvslt #x00000000 ((_ int2bv 32) (str.len __string_1)))))";

    SMTProblem smtProblem = SMTLIBParser.parseSMTProgram(problem);
    Valuation val = new Valuation();
    Result res1 = cvc5.solve(smtProblem.getAllAssertionsAsConjunction(), val);
    assertEquals(SAT, res1);
    val = new Valuation();
    cvc5Context.add(smtProblem.getAllAssertionsAsConjunction());
    Result res = cvc5Context.solve(val);
    assertEquals(SAT, res);
  }

  @Test
  public void debug() throws IOException, SMTLIBParserException {
    String problem = "(declare-fun __double_0 () (_ FloatingPoint 11 53))"+
    "(assert (not (bvsle (ite (fp.isNaN (fp.add (RNE RoundingMode) (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000) __double_0)) #x00000000 (ite (fp.isNegative (fp.add (RNE RoundingMode) (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000) __double_0)) (ite (fp.lt (fp.add (RNE RoundingMode) (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000) __double_0) ((_ to_fp 11 53) (RTZ RoundingMode) #x80000000)) #x80000000 ((_ fp.to_sbv 32) (RTZ RoundingMode) (fp.add (RNE RoundingMode) (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000) __double_0))) (ite (fp.gt (fp.add (RNE RoundingMode) (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000) __double_0) ((_ to_fp 11 53) (RTZ RoundingMode) #x7fffffff)) #x7fffffff ((_ fp.to_sbv 32) (RTZ RoundingMode) (fp.add (RNE RoundingMode) (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000) __double_0))))) #x00000000)))";
    SMTProblem smtProblem = SMTLIBParser.parseSMTProgram(problem);
    Valuation val = new Valuation();
    Result res1 = cvc5.solve(smtProblem.getAllAssertionsAsConjunction(), val);
    assertEquals(SAT, res1);
  }
}
