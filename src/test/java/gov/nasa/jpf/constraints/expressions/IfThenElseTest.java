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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.annotations.Test;

@Test
public class IfThenElseTest {

  @Test(groups = {"expressions", "base"})
  public void testIfThenElse() {

    Variable x = new Variable(BuiltinTypes.BOOL, "x");
    Variable y = new Variable(BuiltinTypes.SINT32, "y");
    Constant c = new Constant(BuiltinTypes.SINT32, 3);

    IfThenElse ite =
        new IfThenElse(
            x,
            new NumericCompound<>(y, NumericOperator.PLUS, c),
            new NumericCompound<>(y, NumericOperator.MINUS, c));

    System.out.println(ite);

    Valuation val = new Valuation();
    val.setValue(y, 10);

    val.setValue(x, true);
    System.out.println(val + ": " + ite.evaluate(val));

    val.setValue(x, false);
    System.out.println(val + ": " + ite.evaluate(val));
  }
}
