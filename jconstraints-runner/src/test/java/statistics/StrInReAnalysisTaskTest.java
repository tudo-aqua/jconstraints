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

package statistics;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import java.io.IOException;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import statistics.callables.StrInReAnalysisTask;

public class StrInReAnalysisTaskTest {
  @Test
  @Disabled
  public void taskTest() throws IOException, SMTLIBParserException {
    String input =
        "(declare-fun var0 () String)(declare-fun var1 () String)(declare-fun var2 ()"
            + " String)(declare-fun var3 () String)(declare-fun var4 () String)(declare-fun var5 ()"
            + " String)(declare-fun var6 () Int)(declare-fun var7 () Int)(declare-fun var8 ()"
            + " Int)(declare-fun var9 () Int)(declare-fun var10 () Int)(declare-fun var11 ()"
            + " Int)(declare-fun var12 () Bool)(declare-fun var13 () Bool)(declare-fun var14 ()"
            + " Bool)(declare-fun var15 () Bool)(declare-fun var16 () Bool)(declare-fun var17 ()"
            + " Bool)(assert (> (str.indexof (str.replace var0 var5 var4) (str.at var2 var9)"
            + " (str.indexof var5 var5 (str.len (str.at var4 var9)))) (str.indexof var2 var2"
            + " (str.indexof (str.substr var2 var9 var8) (str.at var5 var11) (str.len"
            + " var2)))))(assert (> (str.indexof (str.at var4 var11) (str.at var0 8) (str.indexof"
            + " var1 var5 var7)) (str.len var2)))(assert (<= (str.len (str.replace var5 var3 var0))"
            + " (str.indexof (str.replace var0 var0 var2) (str.at var3 var8) (str.indexof var1"
            + " \"f?%Oa6T]f!\" 0))))(assert (not (str.in.re var4 re.allchar)))(assert (str.suffixof"
            + " (str.replace (str.at var3 var8) (str.at var1 var10) (str.at var1 (str.indexof"
            + " (str.at var4 var8) (str.at var4 var6) (str.indexof var3 var5 var6)))) (str.at var3"
            + " var6)))(assert (>= var10 var6))(assert (<= (str.len var5) (str.indexof var0 var4"
            + " var10)))";
    SMTProblem problem = SMTLIBParser.parseSMTProgram(input);
    StrInReAnalysisTask task = new StrInReAnalysisTask(null);
    for (Expression<Boolean> p : problem.assertions) {
      System.out.println(p);
      assert !task.computeAnswer(p);
    }
  }
}
