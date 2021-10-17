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
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

// experimental visitor for creating Ites in the upper levels of a formula
// is of no use at the moment since it has not proved advantageous so far
public class IfThenElseCombinerVisitor extends DuplicatingVisitor<Void> {

  private static final IfThenElseCombinerVisitor INSTANCE = new IfThenElseCombinerVisitor();

  public static IfThenElseCombinerVisitor getInstance() {
    return INSTANCE;
  }

  @Override
  public Expression<?> visit(NumericBooleanExpression n, Void data) {
    Expression leftChild = visit(n.getLeft(), data);
    Expression rightChild = visit(n.getRight(), data);
    NumericComparator comparator = n.getComparator();

    boolean leftChildIsIte = leftChild instanceof IfThenElse;
    boolean rightChildIsIte = rightChild instanceof IfThenElse;

    if (!leftChildIsIte && !rightChildIsIte) {
      return NumericBooleanExpression.create(leftChild, comparator, rightChild);

    } else if (leftChildIsIte && !rightChildIsIte) {
      Expression newThen =
          NumericBooleanExpression.create(
              ((IfThenElse<?>) leftChild).getThen(), comparator, rightChild);
      Expression newElse =
          NumericBooleanExpression.create(
              ((IfThenElse<?>) leftChild).getElse(), comparator, rightChild);
      Expression newIte = IfThenElse.create(((IfThenElse<?>) leftChild).getIf(), newThen, newElse);

      return newIte;
    } else if (!leftChildIsIte && rightChildIsIte) {
      Expression newThen =
          NumericBooleanExpression.create(
              leftChild, comparator, ((IfThenElse<?>) rightChild).getThen());
      Expression newElse =
          NumericBooleanExpression.create(
              leftChild, comparator, ((IfThenElse<?>) rightChild).getElse());
      Expression newIte = IfThenElse.create(((IfThenElse<?>) rightChild).getIf(), newThen, newElse);

      return newIte;

    } else if (leftChildIsIte && rightChildIsIte) {
      Expression leftCondition = ((IfThenElse<?>) leftChild).getIf();
      Expression leftThen = ((IfThenElse<?>) leftChild).getThen();
      Expression leftElse = ((IfThenElse<?>) leftChild).getElse();

      Expression rightCondition = ((IfThenElse<?>) rightChild).getIf();
      Expression rightThen = ((IfThenElse<?>) rightChild).getThen();
      Expression rightElse = ((IfThenElse<?>) rightChild).getElse();

      Expression numeric1 = NumericBooleanExpression.create(leftThen, comparator, rightThen);
      Expression numeric2 = NumericBooleanExpression.create(leftThen, comparator, rightElse);
      Expression numeric3 = NumericBooleanExpression.create(leftElse, comparator, rightThen);
      Expression numeric4 = NumericBooleanExpression.create(leftElse, comparator, rightElse);

      Expression innerInnerIte = IfThenElse.create(rightCondition, numeric1, numeric2);
      Expression innerIte =
          IfThenElse.create(((IfThenElse<?>) leftChild).getIf(), innerInnerIte, numeric3);
      Expression outerIte =
          IfThenElse.create(ExpressionUtil.or(leftCondition, rightCondition), innerIte, numeric4);

      return outerIte;

    } else {
      throw new UnsupportedOperationException("NumericBooleanExpression case is missing!");
    }
  }

  @Override
  public <E> Expression<?> visit(NumericCompound<E> n, Void data) {
    Expression leftChild = visit(n.getLeft(), data);
    Expression rightChild = visit(n.getRight(), data);
    NumericOperator operator = n.getOperator();

    boolean leftChildIsIte = leftChild instanceof IfThenElse;
    boolean rightChildIsIte = rightChild instanceof IfThenElse;

    if (!leftChildIsIte && !rightChildIsIte) {
      return NumericCompound.create(leftChild, operator, rightChild);
    } else if (leftChildIsIte && !rightChildIsIte) {
      Expression newThen =
          NumericCompound.create(((IfThenElse<?>) leftChild).getThen(), operator, rightChild);
      Expression newElse =
          NumericCompound.create(((IfThenElse<?>) leftChild).getElse(), operator, rightChild);
      Expression newIte = IfThenElse.create(((IfThenElse<?>) leftChild).getIf(), newThen, newElse);

      return newIte;
    } else if (!leftChildIsIte && rightChildIsIte) {
      Expression newThen =
          NumericCompound.create(leftChild, operator, ((IfThenElse<?>) rightChild).getThen());
      Expression newElse =
          NumericCompound.create(leftChild, operator, ((IfThenElse<?>) rightChild).getElse());
      Expression newIte = IfThenElse.create(((IfThenElse<?>) rightChild).getIf(), newThen, newElse);

      return newIte;

    } else if (leftChildIsIte && rightChildIsIte) {
      Expression leftCondition = ((IfThenElse<?>) leftChild).getIf();
      Expression leftThen = ((IfThenElse<?>) leftChild).getThen();
      Expression leftElse = ((IfThenElse<?>) leftChild).getElse();

      Expression rightCondition = ((IfThenElse<?>) rightChild).getIf();
      Expression rightThen = ((IfThenElse<?>) rightChild).getThen();
      Expression rightElse = ((IfThenElse<?>) rightChild).getElse();

      Expression numeric1 = NumericCompound.create(leftThen, operator, rightThen);
      Expression numeric2 = NumericCompound.create(leftThen, operator, rightElse);
      Expression numeric3 = NumericCompound.create(leftElse, operator, rightThen);
      Expression numeric4 = NumericCompound.create(leftElse, operator, rightElse);

      Expression innerInnerIte = IfThenElse.create(rightCondition, numeric1, numeric2);
      Expression innerIte =
          IfThenElse.create(((IfThenElse<?>) leftChild).getIf(), innerInnerIte, numeric3);
      Expression outerIte =
          IfThenElse.create(ExpressionUtil.or(leftCondition, rightCondition), innerIte, numeric4);

      return outerIte;
    } else {
      throw new UnsupportedOperationException("NumericCompound case is missing!");
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

  @Override
  public Expression<?> visit(PropositionalCompound n, Void data) {
    Expression leftChild = visit(n.getLeft(), data);
    Expression rightChild = visit(n.getRight(), data);
    LogicalOperator operator = n.getOperator();

    boolean leftChildIsIte = leftChild instanceof IfThenElse;
    boolean rightChildIsIte = rightChild instanceof IfThenElse;

    if (!leftChildIsIte && !rightChildIsIte) {
      return PropositionalCompound.create(leftChild, operator, rightChild);
    } else if (leftChildIsIte && !rightChildIsIte) {
      Expression newThen =
          PropositionalCompound.create(
              (Expression<Boolean>) ((IfThenElse<?>) leftChild).getThen(), operator, rightChild);
      Expression newElse =
          PropositionalCompound.create(
              (Expression<Boolean>) ((IfThenElse<?>) leftChild).getElse(), operator, rightChild);
      Expression newIte = IfThenElse.create(((IfThenElse<?>) leftChild).getIf(), newThen, newElse);

      return newIte;
    } else if (!leftChildIsIte && rightChildIsIte) {
      Expression newThen =
          PropositionalCompound.create(leftChild, operator, ((IfThenElse<?>) rightChild).getThen());
      Expression newElse =
          PropositionalCompound.create(leftChild, operator, ((IfThenElse<?>) rightChild).getElse());
      Expression newIte = IfThenElse.create(((IfThenElse<?>) rightChild).getIf(), newThen, newElse);

      return newIte;
    } else if (leftChildIsIte && rightChildIsIte) {
      Expression leftCondition = ((IfThenElse<?>) leftChild).getIf();
      Expression leftThen = ((IfThenElse<?>) leftChild).getThen();
      Expression leftElse = ((IfThenElse<?>) leftChild).getElse();

      Expression rightCondition = ((IfThenElse<?>) rightChild).getIf();
      Expression rightThen = ((IfThenElse<?>) rightChild).getThen();
      Expression rightElse = ((IfThenElse<?>) rightChild).getElse();

      Expression numeric1 = PropositionalCompound.create(leftThen, operator, rightThen);
      Expression numeric2 = PropositionalCompound.create(leftThen, operator, rightElse);
      Expression numeric3 = PropositionalCompound.create(leftElse, operator, rightThen);
      Expression numeric4 = PropositionalCompound.create(leftElse, operator, rightElse);

      Expression innerInnerIte = IfThenElse.create(rightCondition, numeric1, numeric2);
      Expression innerIte =
          IfThenElse.create(((IfThenElse<?>) leftChild).getIf(), innerInnerIte, numeric3);
      Expression outerIte =
          IfThenElse.create(ExpressionUtil.or(leftCondition, rightCondition), innerIte, numeric4);

      return outerIte;
    } else {
      throw new UnsupportedOperationException("PropositionalCompound case is missing!");
    }
  }
}
