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

public enum Quantifier {
  FORALL("forall") {
    public Quantifier negate() {
      return EXISTS;
    }
  },
  EXISTS("exists") {
    public Quantifier negate() {
      return FORALL;
    }
  };

  private final String str;

  private Quantifier(String str) {
    this.str = str;
  }

  public abstract Quantifier negate();

  @Override
  public String toString() {
    return str;
  }
}
