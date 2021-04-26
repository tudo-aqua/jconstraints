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

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("expressions")
public class PrintTest {

  Expression<Boolean> exprUnderTest;

  @BeforeEach
  public void setupExpression() {
    Variable<Integer> var2 = Variable.create(BuiltinTypes.SINT32, "Y");
    Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 8);

    NumericBooleanExpression bool1 = new NumericBooleanExpression(var2, NumericComparator.EQ, null);
    NumericBooleanExpression bool2 = new NumericBooleanExpression(null, NumericComparator.EQ, c2);
    exprUnderTest = new PropositionalCompound(bool1, LogicalOperator.OR, bool2);
  }

  @Test
  public void testMalformedPrint() {
    StringBuilder builder = new StringBuilder();
    try {
      exprUnderTest.printMalformedExpression(builder);
    } catch (IOException ignored) {
    }
    String result = builder.toString();
    assertTrue(result.contains("null"));
  }

  @Test
  public void testPrint() {
    StringBuilder builder = new StringBuilder();
    assertThrows(
        NullPointerException.class,
        () -> {
          try {
            exprUnderTest.print(builder);
          } catch (IOException ignored) {
          }
        });
  }
}
