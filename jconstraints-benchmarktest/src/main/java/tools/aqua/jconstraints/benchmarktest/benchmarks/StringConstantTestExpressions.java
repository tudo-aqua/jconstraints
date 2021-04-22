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

package tools.aqua.jconstraints.benchmarktest.benchmarks;

import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.SAT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;
import static gov.nasa.jpf.constraints.types.BuiltinTypes.INTEGER;
import static gov.nasa.jpf.constraints.types.BuiltinTypes.STRING;
import static tools.aqua.jconstraints.benchmarktest.benchmarks.StringConstantTestExpressions.Constants.DOLOR;
import static tools.aqua.jconstraints.benchmarktest.benchmarks.StringConstantTestExpressions.Constants.LOREM_IPSUM;
import static tools.aqua.jconstraints.benchmarktest.benchmarks.StringConstantTestExpressions.Constants.ONE;
import static tools.aqua.jconstraints.benchmarktest.benchmarks.StringConstantTestExpressions.Constants.TWO;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringCompoundExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes.StringType;
import java.math.BigInteger;

/**
 * Contains {@link TestCase}s for the handling of various operations on the {@link StringType}
 * containing only {@link Constant}s.
 */
public enum StringConstantTestExpressions implements TestCase {

  // TODO other combinations
  STRING_CONST_EQUALS_CONCAT(
      StringBooleanExpression.createEquals(
          StringCompoundExpression.createConcat(LOREM_IPSUM, DOLOR),
          Constant.create(STRING, "Lorem ipsumdolor")),
      SAT),
  STRING_CONST_EQUALS_SUBSTR(
      StringBooleanExpression.createEquals(
          StringCompoundExpression.createSubstring(LOREM_IPSUM, ONE, TWO),
          Constant.create(STRING, "or")),
      SAT),
  STRING_CONST_EQUALS_AT(
      StringBooleanExpression.createEquals(
          StringCompoundExpression.createAt(LOREM_IPSUM, ONE), Constant.create(STRING, "o")),
      SAT),
  STRING_CONST_EQUALS_TOSTR(
      StringBooleanExpression.createEquals(
          StringCompoundExpression.createToString(ONE), Constant.create(STRING, "1")),
      SAT),
  STRING_CONST_EQUALS_REPLACE(
      StringBooleanExpression.createEquals(
          StringCompoundExpression.createReplace(
              LOREM_IPSUM, Constant.create(STRING, "ipsum"), DOLOR),
          Constant.create(STRING, "Lorem dolor")),
      SAT),

  // TODO Replaceall has no print and throws error
  //		STRING_CONST_EQUALS_REPLACEALL(
  //				StringBooleanExpression.createEquals(
  //						StringCompoundExpression.createReplaceAll(const_Lorem_Ipsum,
  // Constant.create(BuiltinTypes.STRING, "m"), const_Dolor),
  //						Constant.create(BuiltinTypes.STRING, "Loredolor ipsudolor")), Result.SAT);

  // TODO these both have no visit
  //		STRING_CONST_EQUALS_TOLOWERCASE(
  //				StringBooleanExpression.createEquals(
  //						StringCompoundExpression.createToLower(const_Lorem_Ipsum),
  //						Constant.create(BuiltinTypes.STRING, "lorem ipsum")), Result.SAT),
  //		STRING_CONST_EQUALS_TOUPPERCASE(
  //				StringBooleanExpression.createEquals(
  //						StringCompoundExpression.createToUpper(const_Lorem_Ipsum),
  //						Constant.create(BuiltinTypes.STRING, "LOREM IPSUM")), Result.SAT);

  STRING_CONST_CONTAINS_CONCAT(
      StringBooleanExpression.createContains(
          StringCompoundExpression.createConcat(LOREM_IPSUM, DOLOR),
          Constant.create(STRING, "Lorem")),
      SAT),

  STRING_CONST_PREFIXOF_CONCAT(
      StringBooleanExpression.createPrefixOf(
          StringCompoundExpression.createConcat(LOREM_IPSUM, DOLOR),
          Constant.create(STRING, "Lorem")),
      SAT),

  STRING_CONST_SUFFIXOF_CONCAT(
      StringBooleanExpression.createSuffixOf(
          StringCompoundExpression.createConcat(LOREM_IPSUM, DOLOR),
          Constant.create(STRING, "dolor")),
      SAT),

  STRING_CONST_LENGTH_CONCAT(
      NumericBooleanExpression.create(
          StringIntegerExpression.createLength(
              StringCompoundExpression.createConcat(LOREM_IPSUM, DOLOR)),
          EQ,
          Constant.create(INTEGER, BigInteger.valueOf(16))),
      SAT),

  STRING_CONST_INDEXOF_CONCAT(
      NumericBooleanExpression.create(
          StringIntegerExpression.createIndexOf(
              StringCompoundExpression.createConcat(LOREM_IPSUM, DOLOR),
              Constant.create(STRING, "dolor")),
          EQ,
          Constant.create(INTEGER, BigInteger.valueOf(11))),
      SAT),

  STRING_CONST_TOINT_CONCAT(
      NumericBooleanExpression.create(
          StringIntegerExpression.createToInt(
              StringCompoundExpression.createConcat(
                  Constant.create(STRING, "1"), Constant.create(STRING, "2"))),
          EQ,
          Constant.create(INTEGER, BigInteger.valueOf(12))),
      SAT);

  static final class Constants {
    static final Constant<String> LOREM_IPSUM = Constant.create(STRING, "Lorem ipsum");
    static final Constant<String> DOLOR = Constant.create(STRING, "dolor");
    static final Constant<String> SIT = Constant.create(STRING, "sit");
    static final Constant<String> AMET = Constant.create(STRING, "amet");
    static final Constant<String> SPACE = Constant.create(STRING, " ");

    static final Constant<BigInteger> ONE = Constant.create(INTEGER, BigInteger.valueOf(1));
    static final Constant<BigInteger> TWO = Constant.create(INTEGER, BigInteger.valueOf(2));
  }

  private final Expression<Boolean> test;
  private final Result expected;

  StringConstantTestExpressions(Expression<Boolean> expr, Result result) {
    this.test = expr;
    this.expected = result;
  }

  @Override
  public Expression<Boolean> getTest() {
    return this.test;
  }

  @Override
  public Result getExpectedResult() {
    return this.expected;
  }

  @Override
  public String getName() {
    return this.toString();
  }
}
