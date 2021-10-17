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

/** operator for logic formulas */
public enum LogicalOperator implements ExpressionOperator {
  AND("&&") {
    public LogicalOperator invert() {
      return OR;
    }

    @Override
    public boolean eval(final boolean lv, final boolean rv) {
      return lv && rv;
    }
  },
  OR("||") {
    public LogicalOperator invert() {
      return AND;
    }

    @Override
    public boolean eval(final boolean lv, final boolean rv) {
      return lv || rv;
    }
  },
  IMPLY("->") {
    public LogicalOperator invert() {
      throw new UnsupportedOperationException("IMPLY cannot be inverted to a LogicalOperator");
    }

    @Override
    public boolean eval(final boolean lv, final boolean rv) {
      return !lv || rv;
    }
  },
  EQUIV("<->") {
    public LogicalOperator invert() {
      return XOR;
    }

    @Override
    public boolean eval(final boolean lv, final boolean rv) {
      return lv == rv;
    }
  },
  XOR("^") {
    public LogicalOperator invert() {
      return EQUIV;
    }

    @Override
    public boolean eval(final boolean lv, final boolean rv) {
      return lv ^ rv;
    }
  };

  private final String str;

  private LogicalOperator(final String str) {
    this.str = str;
  }

  @Override
  public String toString() {
    return str;
  }

  public static LogicalOperator fromString(final String str) {
    switch (str) {
      case "&&":
        return AND;
      case "||":
        return OR;
      case "=>":
      case "->":
        return IMPLY;
      case "<->":
        return EQUIV;
      case "^":
        return XOR;
      default:
        return null;
    }
  }

  public abstract boolean eval(boolean lv, boolean rv);

  public abstract LogicalOperator invert();
}
