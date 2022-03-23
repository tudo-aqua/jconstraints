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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.types.BuiltinTypes;

public enum FPRoundingMode {
  RNE,
  RNA,
  RTP,
  RTN,
  RTZ;

  public static final Constant ROUNDING_MODE_SYMBOL =
      new Constant(BuiltinTypes.STRING, "RoundingMode");

  public static FPRoundingMode fromString(String str) {
    switch (str) {
      case "RNE":
        return RNE;
      case "RNA":
        return RNA;
      case "RTP":
        return RTP;
      case "RTN":
        return RTN;
      case "RTZ":
        return RTZ;
      default:
        throw new IllegalArgumentException("unsupported rounding mode: " + str);
    }
  }
}
