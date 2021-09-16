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

/** operator on numbers */
public enum NumericOperator implements ExpressionOperator {
  DIV("/"),
  MUL("*"),
  MINUS("-"),
  PLUS("+"),
  REM("%"),
  MOD("MOD");

  private final String str;

  NumericOperator(String str) {
    this.str = str;
  }

  @Override
  public String toString() {
    return str;
  }

  public static NumericOperator fromString(String str) {
    switch (str.toLowerCase()) {
      case "/":
        return DIV;
      case "*":
        return MUL;
        // case "bvsub":
      case "-":
        return MINUS;
        // case "bvadd":
      case "+":
        return PLUS;
      case "rem":
      case "%":
        return REM;
      case "mod":
        return MOD;
      default:
        return null;
    }
  }
}
