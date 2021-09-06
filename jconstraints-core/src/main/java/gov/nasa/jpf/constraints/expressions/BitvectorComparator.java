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

/** bitvector comparator */
public enum BitvectorComparator implements ExpressionOperator {
  EQ("=") {
    public BitvectorComparator not() {
      return NE;
    }

    public boolean eval(int cmpResult) {
      return (cmpResult == 0);
    }
  },
  NE("!=") {
    public BitvectorComparator not() {
      return EQ;
    }

    public boolean eval(int cmpResult) {
      return (cmpResult != 0);
    }
  },
  SLT("bvslt") {
    public BitvectorComparator not() {
      return SGE;
    }

    public boolean eval(int cmpResult) {
      return (cmpResult < 0);
    }
  },
  SLE("bvsle") {
    public BitvectorComparator not() {
      return SGT;
    }

    public boolean eval(int cmpResult) {
      return (cmpResult <= 0);
    }
  },
  SGT("bvsgt") {
    public BitvectorComparator not() {
      return SLE;
    }

    public boolean eval(int cmpResult) {
      return (cmpResult > 0);
    }
  },
  SGE("bvsge") {
    public BitvectorComparator not() {
      return SLT;
    }

    public boolean eval(int cmpResult) {
      return (cmpResult >= 0);
    }
  },
  ULT("bvult") {
    public BitvectorComparator not() {
      return UGE;
    }

    public boolean eval(int cmpResult) {
      return (cmpResult < 0);
    }
  },
  ULE("bvule") {
    public BitvectorComparator not() {
      return UGT;
    }

    public boolean eval(int cmpResult) {
      return (cmpResult <= 0);
    }
  },
  UGT("bvugt") {
    public BitvectorComparator not() {
      return ULE;
    }

    public boolean eval(int cmpResult) {
      return (cmpResult > 0);
    }
  },
  UGE("bvuge") {
    public BitvectorComparator not() {
      return ULT;
    }

    public boolean eval(int cmpResult) {
      return (cmpResult >= 0);
    }
  };

  private final String str;

  BitvectorComparator(String str) {
    this.str = str;
  }

  public static BitvectorComparator fromString(String str) {
    switch (str) {
      case "=":
        return EQ;
      case "!=":
        return NE;
      case "bvslt":
        return SLT;
      case "bvsle":
        return SLE;
      case "bvsgt":
        return SGT;
      case "bvsge":
        return SGE;
      case "bvult":
        return ULT;
      case "bvule":
        return ULE;
      case "bvugt":
        return UGT;
      case "bvuge":
        return UGE;
      default:
        return null;
    }
  }

  public abstract BitvectorComparator not();

  public abstract boolean eval(int cmpResult);

  @Override
  public String toString() {
    return str;
  }
}
