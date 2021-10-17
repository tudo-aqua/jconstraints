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

package gov.nasa.jpf.constraints.normalization;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;

public class ImplicationRemoverVisitor extends DuplicatingVisitor<Void> {

  private static final ImplicationRemoverVisitor INSTANCE = new ImplicationRemoverVisitor();

  public static ImplicationRemoverVisitor getInstance() {
    return INSTANCE;
  }

  @Override
  public Expression<?> visit(PropositionalCompound expression, Void data) {
    Expression<?> left = visit(expression.getLeft(), data);
    Expression<?> right = visit(expression.getRight(), data);
    LogicalOperator operator = expression.getOperator();

    if (operator.equals(LogicalOperator.IMPLY)) {
      Expression<Boolean> partLeft = Negation.create((Expression<Boolean>) left);
      return PropositionalCompound.create(partLeft, LogicalOperator.OR, right);
    } else {
      return PropositionalCompound.create((Expression<Boolean>) left, operator, right);
    }
  }

  // no deeper visit needed here
  public Expression<?> visit(NumericBooleanExpression n, Void data) {
    return n;
  }

  public <T> Expression<T> apply(Expression<T> expr, Void data) {
    return visit(expr, data).requireAs(expr.getType());
  }
}
