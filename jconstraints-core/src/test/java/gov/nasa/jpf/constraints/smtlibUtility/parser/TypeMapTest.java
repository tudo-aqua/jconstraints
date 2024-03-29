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

package gov.nasa.jpf.constraints.smtlibUtility.parser;

import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.math.BigInteger;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("jsmtlib")
public class TypeMapTest {

  @Test
  public void integerMapTest() {
    assertEquals(TypeMap.<BigInteger>getType("int"), BuiltinTypes.INTEGER);
    assertEquals(TypeMap.<BigInteger>getType("InT"), BuiltinTypes.INTEGER);
    assertEquals(TypeMap.<BigInteger>getType("iNT"), BuiltinTypes.INTEGER);
    assertEquals(TypeMap.<BigInteger>getType("Int"), BuiltinTypes.INTEGER);
    assertEquals(TypeMap.<BigInteger>getType("INT"), BuiltinTypes.INTEGER);
  }
}
