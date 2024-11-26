/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2024 The jConstraints Authors
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
import gov.nasa.jpf.constraints.expressions.*;
import java.util.ArrayList;

public abstract class DuplicatingVisitor<D> extends AbstractExpressionVisitor<Expression<?>, D> {

  @Override
  public <E> Expression<?> visit(IfThenElse<E> n, D data) {
    Expression conditionE = visit(n.getIf(), data);
    Expression thenE = visit(n.getThen(), data);
    Expression elseE = visit(n.getElse(), data);
    return IfThenElse.create(conditionE, thenE, elseE);
  }

  @Override
  public Expression<?> visit(StringIntegerExpression n, D data) {
    Expression right = n.getRight(), offset = n.getOffset();
    return new StringIntegerExpression(
        visit(n.getLeft(), data),
        n.getOperator(),
        right != null ? visit(right, data) : null,
        offset != null ? visit(offset, data) : null);
  }

  @Override
  public Expression<?> visit(StringCompoundExpression n, D data) {
    Expression main, dst, offset, length, position, src;
    Expression[] expressions;
    main = n.getMain();
    dst = n.getDst();
    offset = n.getOffset();
    length = n.getLength();
    position = n.getPosition();
    src = n.getSrc();
    expressions = n.getExpressions();
    Expression<?> duplicateMain = main != null ? visit(main, data) : null;
    Expression<?> duplicateDst = dst != null ? visit(dst, data) : null;
    Expression<?> duplicateOffset = offset != null ? visit(offset, data) : null;
    Expression<?> duplicateLength = length != null ? visit(length, data) : null;
    Expression<?> duplicatePosition = position != null ? visit(position, data) : null;
    Expression<?> duplicateSrc = src != null ? visit(src, data) : null;
    Expression<?>[] duplicateExpressions = null;
    if (expressions != null && expressions.length > 0) {
      ArrayList<Expression<?>> newExpressions = new ArrayList<>();
      for (Expression e : expressions) {
        newExpressions.add(visit(e, data));
      }
      duplicateExpressions = newExpressions.toArray(new Expression[0]);
    }

    return new StringCompoundExpression(
        duplicateMain,
        n.getOperator(),
        duplicateExpressions,
        duplicateOffset,
        duplicateLength,
        duplicateSrc,
        duplicateDst,
        duplicatePosition);
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
