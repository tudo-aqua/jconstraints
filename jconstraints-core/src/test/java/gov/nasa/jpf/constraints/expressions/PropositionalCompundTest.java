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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.EvaluationException;
import gov.nasa.jpf.constraints.simplifiers.TailoringVisitor;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.HashSet;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("expressions")
public class PropositionalCompundTest {

  @Test
  public void negationTest() {
    Variable<Boolean> a = Variable.create(BuiltinTypes.BOOL, "a");
    Variable<Boolean> b = Variable.create(BuiltinTypes.BOOL, "b");

    Expression<Boolean> firstNegation = ExpressionUtil.and(new Negation(a), new Negation(b));
    Expression<Boolean> secondNegation = new Negation(firstNegation);

    assertEquals(secondNegation, secondNegation);

    HashSet<Variable<?>> vars = new HashSet<>();
    vars.add(a);
    vars.add(b);

    Expression<Boolean> duplicated = secondNegation.accept(TailoringVisitor.getInstance(), vars);
    assertEquals(duplicated, secondNegation);
  }

  @Test
  public void emptyValuationThrowsError() {
    Variable<Boolean> a = Variable.create(BuiltinTypes.BOOL, "a");
    Variable<Boolean> b = Variable.create(BuiltinTypes.BOOL, "b");

    PropositionalCompound pc = PropositionalCompound.create(a, LogicalOperator.EQUIV, b);
    assertThrows(EvaluationException.class, () -> pc.evaluate(new Valuation()));
  }
}
