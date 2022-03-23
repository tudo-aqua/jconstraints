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

package gov.nasa.jpf.constraints.smtsemantics;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.StringCompoundExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.math.BigInteger;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("string-expressions")
public class StringTest {

  @Test
  public void chatAtTest() {
    Variable<String> x = Variable.create(BuiltinTypes.STRING, "x");
    Constant<BigInteger> c0 = Constant.create(BuiltinTypes.INTEGER, BigInteger.ZERO);
    StringCompoundExpression expr = StringCompoundExpression.createAt(x, c0);
    Valuation val = new Valuation();
    val.setValue(x, "a");
    assertEquals(expr.evaluate(val), "a");
    assertEquals(expr.evaluateSMT(val), "a");
    val.setValue(x, "");
    assertEquals(expr.evaluateSMT(val), "");
  }

  @Test
  public void chatAtExceptionTest() {
    Variable<String> x = Variable.create(BuiltinTypes.STRING, "x");
    Constant<BigInteger> c0 = Constant.create(BuiltinTypes.INTEGER, BigInteger.ZERO);
    StringCompoundExpression expr = StringCompoundExpression.createAt(x, c0);
    Valuation val = new Valuation();
    val.setValue(x, "");
    assertThrows(StringIndexOutOfBoundsException.class, () -> expr.evaluate(val));
  }
}
