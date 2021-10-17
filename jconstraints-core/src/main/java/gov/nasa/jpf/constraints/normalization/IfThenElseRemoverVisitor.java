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
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

public class IfThenElseRemoverVisitor extends DuplicatingVisitor<Void> {

  private static final IfThenElseRemoverVisitor INSTANCE = new IfThenElseRemoverVisitor();

  public static IfThenElseRemoverVisitor getInstance() {
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
      Expression leftCondition = ((IfThenElse<?>) leftChild).getIf();
      Expression leftThen = ((IfThenElse<?>) leftChild).getThen();
      Expression leftElse = ((IfThenElse<?>) leftChild).getElse();

      Expression compound1 = NumericBooleanExpression.create(leftThen, comparator, rightChild);
      Expression compound2 = NumericBooleanExpression.create(leftElse, comparator, rightChild);

      Expression propositional1 =
          ExpressionUtil.and(leftCondition, (Expression<Boolean>) visit(compound1, data));
      Expression propositional2 =
          ExpressionUtil.and(
              Negation.create(leftCondition), (Expression<Boolean>) visit(compound2, data));

      Expression result = ExpressionUtil.or(propositional1, propositional2);

      return result;

    } else if (!leftChildIsIte && rightChildIsIte) {
      Expression rightCondition = ((IfThenElse<?>) rightChild).getIf();
      Expression rightThen = ((IfThenElse<?>) rightChild).getThen();
      Expression rightElse = ((IfThenElse<?>) rightChild).getElse();

      Expression compound1 = NumericBooleanExpression.create(leftChild, comparator, rightThen);
      Expression compound2 = NumericBooleanExpression.create(leftChild, comparator, rightElse);

      Expression propositional1 =
          ExpressionUtil.and((Expression<Boolean>) visit(compound1, data), rightCondition);
      Expression propositional2 =
          ExpressionUtil.and(
              (Expression<Boolean>) visit(compound2, data), Negation.create(rightCondition));

      Expression result = ExpressionUtil.or(propositional1, propositional2);

      return result;

    } else if (leftChildIsIte && rightChildIsIte) {
      Expression leftCondition = ((IfThenElse<?>) leftChild).getIf();
      Expression leftThen = ((IfThenElse<?>) leftChild).getThen();
      Expression leftElse = ((IfThenElse<?>) leftChild).getElse();

      Expression rightCondition = ((IfThenElse<?>) rightChild).getIf();
      Expression rightThen = ((IfThenElse<?>) rightChild).getThen();
      Expression rightElse = ((IfThenElse<?>) rightChild).getElse();

      Expression compound1 = NumericBooleanExpression.create(leftThen, comparator, rightThen);
      Expression compound2 = NumericBooleanExpression.create(leftThen, comparator, rightElse);
      Expression compound3 = NumericBooleanExpression.create(leftElse, comparator, rightThen);
      Expression compound4 = NumericBooleanExpression.create(leftElse, comparator, rightElse);

      Expression propositional1 =
          ExpressionUtil.and(
              leftCondition, (Expression<Boolean>) visit(compound1, data), rightCondition);
      Expression propositional2 =
          ExpressionUtil.and(
              leftCondition,
              (Expression<Boolean>) visit(compound2, data),
              Negation.create(rightCondition));
      Expression propositional3 =
          ExpressionUtil.and(
              Negation.create(leftCondition),
              (Expression<Boolean>) visit(compound3, data),
              rightCondition);
      Expression propositional4 =
          ExpressionUtil.and(
              Negation.create(leftCondition),
              (Expression<Boolean>) visit(compound4, data),
              Negation.create(rightCondition));

      Expression result =
          ExpressionUtil.or(propositional1, propositional2, propositional3, propositional4);

      return result;

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
  public <E> Expression<?> visit(IfThenElse<E> n, Void data) {
    Expression ifCond = visit(n.getIf(), data);
    Expression thenExpr = visit(n.getThen(), data);
    Expression elseExpr = visit(n.getElse(), data);

    if (thenExpr.getType().equals(BuiltinTypes.BOOL)
        && elseExpr.getType().equals(BuiltinTypes.BOOL)) {
      Expression firstPart = ExpressionUtil.or(Negation.create(ifCond), thenExpr);
      Expression secondPart = ExpressionUtil.or(ifCond, elseExpr);

      // visit again for finding nested IfThenElse
      Expression result = ExpressionUtil.and((Expression<Boolean>) firstPart, secondPart);

      return result;
    } else {
      // a numeric IfThenElse in a numeric IfThenElse will return here unflattened
      return IfThenElse.create(ifCond, thenExpr, elseExpr);
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
