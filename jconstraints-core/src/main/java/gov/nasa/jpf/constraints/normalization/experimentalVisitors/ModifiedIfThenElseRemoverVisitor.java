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

package gov.nasa.jpf.constraints.normalization.experimentalVisitors;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;

// only boolean flattening for testing; numeric Ites are simply returned
public class ModifiedIfThenElseRemoverVisitor extends DuplicatingVisitor<Void> {

  private static final ModifiedIfThenElseRemoverVisitor INSTANCE =
      new ModifiedIfThenElseRemoverVisitor();

  public static ModifiedIfThenElseRemoverVisitor getInstance() {
    return INSTANCE;
  }

  @Override
  public Expression<?> visit(NumericBooleanExpression n, Void data) {
    return n;
  }

  @Override
  public <E> Expression<?> visit(NumericCompound<E> n, Void data) {
    return n;
  }

  @Override
  public <E> Expression<?> visit(IfThenElse<E> n, Void data) {
    Expression ifCond = n.getIf();
    Expression thenExpr = visit(n.getThen(), data);
    Expression elseExpr = visit(n.getElse(), data);

    if (thenExpr.getType().equals(BuiltinTypes.BOOL)
        && elseExpr.getType().equals(BuiltinTypes.BOOL)) {
      Expression firstPart =
          PropositionalCompound.create(Negation.create(ifCond), LogicalOperator.OR, thenExpr);
      Expression secondPart = PropositionalCompound.create(ifCond, LogicalOperator.OR, elseExpr);

      // visit again for finding nested IfThenElse
      Expression result =
          PropositionalCompound.create(
              (Expression<Boolean>) firstPart, LogicalOperator.AND, secondPart);

      return result;
    } else {
      // a numeric IfThenElse in a numeric IfThenElse will return here unflattened
      return n;
    }
  }

  @Override
  // Not needed if LetExpressionRemover is used beforehand
  public Expression<?> visit(LetExpression let, Void data) {
    return visit(let.flattenLetExpression(), data);
  }

  public <T> Expression<T> apply(Expression<T> expr, Void data) {
    return visit(expr, data).requireAs(expr.getType());
  }
}
