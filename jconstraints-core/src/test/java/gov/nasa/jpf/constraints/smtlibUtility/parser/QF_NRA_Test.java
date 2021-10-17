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

package gov.nasa.jpf.constraints.smtlibUtility.parser;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.IOException;
import java.util.Set;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

/**
 * All test cases in this test case are taken from the QF_NRA section of the SMT competition 2018.
 *
 * @author Malte Mues (@mmuesly)
 */
@Tag("base")
@Tag("jsmtlib")
public class QF_NRA_Test {
  @Test
  public void realParsingGen09Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/gen-09.smt2");

    final Expression<Boolean> singleExpr = problem.getAllAssertionsAsConjunction();
    final Set<Variable<?>> vars = ExpressionUtil.freeVariables(singleExpr);

    for (final Variable<?> v : vars) {
      assertEquals(v.getType(), BuiltinTypes.DECIMAL);
    }
    final Expression<Boolean> firstAssertion = problem.assertions.get(0);
    assertEquals(firstAssertion.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression castedFirstAssertion = (NumericBooleanExpression) firstAssertion;
    assertEquals(castedFirstAssertion.getComparator(), NumericComparator.EQ);

    final Expression<Boolean> secondAssertion = problem.assertions.get(1);
    assertEquals(secondAssertion.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression castedSecondAssertion =
        (NumericBooleanExpression) secondAssertion;
    assertEquals(castedSecondAssertion.getComparator(), NumericComparator.EQ);

    final Expression<Boolean> thirdAssertion = problem.assertions.get(2);
    assertEquals(thirdAssertion.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression castedThirdAssertion = (NumericBooleanExpression) thirdAssertion;
    assertEquals(castedThirdAssertion.getComparator(), NumericComparator.GT);
    assertEquals(((Variable<?>) castedThirdAssertion.getLeft()).getName(), "b");
    assertEquals(((Variable<?>) castedThirdAssertion.getRight()).getName(), "a");
  }

  @Test
  public void realParsingGen14Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/gen-14.smt2");
    final Expression<Boolean> assertStmt = problem.assertions.get(0);
    assertEquals(assertStmt.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression castedAssertStmt = (NumericBooleanExpression) assertStmt;
    assertEquals(castedAssertStmt.getRight().getClass(), UnaryMinus.class);
    assertEquals(castedAssertStmt.getRight().getType(), BuiltinTypes.DECIMAL);
  }

  @Test
  public void realParsingMgc02Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/mgc_02.smt2");
    assertEquals(problem.assertions.size(), 1);
    final Expression<Boolean> assertion = problem.assertions.get(0);
    assertEquals(assertion.getType(), BuiltinTypes.BOOL);

    final Set<Variable<?>> vars = ExpressionUtil.freeVariables(assertion);
    for (final Variable<?> v : vars) {
      assertEquals(v.getType(), BuiltinTypes.DECIMAL);
    }
  }
}
