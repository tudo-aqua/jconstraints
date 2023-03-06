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

package gov.nasa.jpf.constraints.expressions;

import static org.junit.jupiter.api.Assertions.assertThrows;

import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("expressions")
public class NumericBooleanExpressionTest {

  /*
   * An equivalence between two boolean objects should be checked using a propositional compound and
   * the equivalence operator.
   */
  @Test
  public void createBooleanExpressionTest() {
    Constant<Boolean> f = new Constant(BuiltinTypes.BOOL, false);
    Variable<Boolean> var = Variable.create(BuiltinTypes.BOOL, "x");
    assertThrows(
        AssertionError.class,
        () -> {
          NumericBooleanExpression.create(var, NumericComparator.EQ, f);
        });
  }
}
