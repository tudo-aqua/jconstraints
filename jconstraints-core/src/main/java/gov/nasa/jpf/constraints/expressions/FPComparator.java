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

public enum FPComparator implements ExpressionOperator {
  FPEQ("fp.eq"),
  FPLT("fp.lt"),
  FPLE("fp.leq"),
  FPGT("fp.gt"),
  FPGE("fp.geq"),
  FP_IS_NAN("fp.isNaN"),
  FP_IS_NEGATIVE("fp.isNegative");
  //FIXME: add missing!!!!

  private final String str;

  FPComparator(String str) {
    this.str = str;
  }

  @Override
  public String toString() {
    return str;
  }

  public static FPComparator fromString(String str) {
    switch (str) {
      case "fp.eq":
        return FPEQ;
      case "fp.lt":
        return FPLT;
      case "fp.leq":
        return FPLE;
      case "fp.gt":
        return FPGT;
      case "fp.geq":
        return FPGE;
      case "fp.isNaN":
        return FP_IS_NAN;
      case "fp.isNegative":
        return FP_IS_NEGATIVE;
    }
    return null;
  }
}
