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

package gov.nasa.jpf.constraints.util;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.IfThenElse;

public abstract class DuplicatingVisitor<D> extends AbstractExpressionVisitor<Expression<?>, D> {

  @Override
  public <E> Expression<?> visit(IfThenElse<E> n, D data) {
    Expression conditionE = visit(n.getIf(), data);
    Expression thenE = visit(n.getThen(), data);
    Expression elseE = visit(n.getElse(), data);
    return IfThenElse.create(conditionE, thenE, elseE);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.AbstractExpressionVisitor#defaultVisit(gov.nasa.jpf.constraints.api.Expression, java.lang.Object)
   */
  @Override
  protected <E> Expression<?> defaultVisit(Expression<E> expression, D data) {
    Expression<?>[] children = expression.getChildren();
    boolean changed = false;
    for (int i = 0; i < children.length; i++) {
      Expression<?> c = children[i];
      Expression<?> r = visit(c, data);
      if (c != r) changed = true;
      children[i] = r;
    }
    if (!changed) return expression;
    return expression.duplicate(children);
  }
}
