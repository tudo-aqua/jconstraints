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
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

public class SimplifyProblemVisitor extends DuplicatingVisitor<Void> {

  private static final SimplifyProblemVisitor INSTANCE = new SimplifyProblemVisitor();

  public static SimplifyProblemVisitor getInstance() {
    return INSTANCE;
  }

  @Override
  public Expression<?> visit(PropositionalCompound n, Void data) {
    Expression leftChild = visit(n.getLeft(), data);
    Expression rightChild = visit(n.getRight(), data);
    LogicalOperator operator = n.getOperator();

    if (operator.equals(LogicalOperator.EQUIV)) {
      if (leftChild.equals(rightChild)) {
        return Constant.create(BuiltinTypes.BOOL, Boolean.TRUE);
      }
      if (leftChild instanceof Constant) {
        if (((Constant<?>) leftChild).getValue().equals(Boolean.TRUE)) {
          return rightChild;
        }
      }
      if (rightChild instanceof Constant) {
        if (((Constant<?>) rightChild).getValue().equals(Boolean.TRUE)) {
          return leftChild;
        }
      }
      if (leftChild instanceof Constant) {
        if (((Constant<?>) leftChild).getValue().equals(Boolean.FALSE)) {
          if (rightChild.getType().equals(BuiltinTypes.BOOL)) {
            return Negation.create(rightChild);
          }
        }
      }
      if (rightChild instanceof Constant) {
        if (((Constant<?>) rightChild).getValue().equals(Boolean.FALSE)) {
          if (leftChild.getType().equals(BuiltinTypes.BOOL)) {
            return Negation.create(leftChild);
          }
        }
      }
    }

    if (operator.equals(LogicalOperator.IMPLY)) {
      if (rightChild instanceof Constant) {
        if (((Constant<?>) rightChild).getValue().equals(Boolean.TRUE)) {
          return Constant.create(BuiltinTypes.BOOL, Boolean.TRUE);
        }
      }
      if (rightChild instanceof Constant) {
        if (((Constant<?>) rightChild).getValue().equals(Boolean.FALSE)) {
          return Negation.create(leftChild);
        }
      }
      if (leftChild.equals(rightChild)) {
        return Constant.create(BuiltinTypes.BOOL, Boolean.TRUE);
      }
      if (leftChild instanceof Constant) {
        if (((Constant<?>) leftChild).getValue().equals(Boolean.TRUE)) {
          return rightChild;
        }
      }
      if (leftChild instanceof Constant) {
        if (((Constant<?>) leftChild).getValue().equals(Boolean.FALSE)) {
          return Constant.create(BuiltinTypes.BOOL, Boolean.TRUE);
        }
      }
    }

    if (operator.equals(LogicalOperator.AND)) {
      // removal of obvious duplicates
      if (leftChild.equals(rightChild)) {
        // or rightChild
        return leftChild;
      }
      if (leftChild instanceof Negation) {
        if (rightChild.equals(((Negation) leftChild).getNegated())) {
          return Constant.create(BuiltinTypes.BOOL, Boolean.FALSE);
        }
      }
      if (rightChild instanceof Negation) {
        if (leftChild.equals(((Negation) rightChild).getNegated())) {
          return Constant.create(BuiltinTypes.BOOL, Boolean.FALSE);
        }
      }
      if (leftChild instanceof Constant) {
        if (((Constant<?>) leftChild).getValue().equals(Boolean.FALSE)) {
          return Constant.create(BuiltinTypes.BOOL, Boolean.FALSE);
        }
      }
      if (rightChild instanceof Constant) {
        if (((Constant<?>) rightChild).getValue().equals(Boolean.FALSE)) {
          return Constant.create(BuiltinTypes.BOOL, Boolean.FALSE);
        }
      }
      if (leftChild instanceof Constant) {
        if (((Constant<?>) leftChild).getValue().equals(Boolean.TRUE)) {
          return rightChild;
        }
      }
      if (rightChild instanceof Constant) {
        if (((Constant<?>) rightChild).getValue().equals(Boolean.TRUE)) {
          return leftChild;
        }
      }
    }
    if (operator.equals(LogicalOperator.OR)) {
      // removal of obvious duplicates
      if (leftChild.equals(rightChild)) {
        // or rightChild
        return leftChild;
      }
      if (leftChild instanceof Negation) {
        if (rightChild.equals(((Negation) leftChild).getNegated())) {
          return Constant.create(BuiltinTypes.BOOL, Boolean.TRUE);
        }
      }
      if (rightChild instanceof Negation) {
        if (leftChild.equals(((Negation) rightChild).getNegated())) {
          return Constant.create(BuiltinTypes.BOOL, Boolean.TRUE);
        }
      }
      if (leftChild instanceof Constant) {
        if (((Constant<?>) leftChild).getValue().equals(Boolean.TRUE)) {
          return Constant.create(BuiltinTypes.BOOL, Boolean.TRUE);
        }
      }
      if (rightChild instanceof Constant) {
        if (((Constant<?>) rightChild).getValue().equals(Boolean.TRUE)) {
          return Constant.create(BuiltinTypes.BOOL, Boolean.TRUE);
        }
      }
      if (leftChild instanceof Constant) {
        if (((Constant<?>) leftChild).getValue().equals(Boolean.FALSE)) {
          return rightChild;
        }
      }
      if (rightChild instanceof Constant) {
        if (((Constant<?>) rightChild).getValue().equals(Boolean.FALSE)) {
          return leftChild;
        }
      }
    }

    return PropositionalCompound.create(leftChild, operator, rightChild);
  }

  @Override
  public Expression<?> visit(Negation n, Void data) {
    Expression negated = visit(n.getNegated(), data);

    if (negated.equals(ExpressionUtil.TRUE)) {
      return Constant.create(BuiltinTypes.BOOL, Boolean.FALSE);
    }
    if (negated.equals(ExpressionUtil.FALSE)) {
      return Constant.create(BuiltinTypes.BOOL, Boolean.TRUE);
    }
    return Negation.create(negated);
  }

  @Override
  public Expression<?> visit(NumericBooleanExpression n, Void data) {
    Expression leftChild = visit(n.getLeft(), data);
    Expression rightChild = visit(n.getRight(), data);

    if (n.getComparator().equals(NumericComparator.EQ)) {
      if (n.getLeft().equals(n.getRight())) {
        return Constant.create(BuiltinTypes.BOOL, Boolean.TRUE);
      }
    }
    if (n.getComparator().equals(NumericComparator.NE)) {
      if (n.getLeft().equals(n.getRight())) {
        return Constant.create(BuiltinTypes.BOOL, Boolean.FALSE);
      }
    }
    return NumericBooleanExpression.create(leftChild, n.getComparator(), rightChild);
  }

  @Override
  public Expression<?> visit(QuantifierExpression q, Void data) {
    Expression body = visit(q.getBody(), data);
    List<? extends Variable<?>> bound = q.getBoundVariables();
    Set<Variable<?>> freeVars = ExpressionUtil.freeVariables(body);
    // newBound is used to delete bound variables which aren't free in body
    List<Variable<?>> newBound = new ArrayList<>();
    boolean boundInFree = false;

    if (freeVars != null) {
      for (Variable v : bound) {
        for (Variable f : freeVars) {
          if (f.equals(v) && !newBound.contains(v)) {
            newBound.add(v);
            boundInFree = true;
            break;
          }
        }
      }
    }

    // case: quantifier binds no variables which are free in body
    if (!boundInFree) {
      return body;
    } else {
      return QuantifierExpression.create(q.getQuantifier(), newBound, body);
    }
  }

  @Override
  // Not needed if LetExpressionRemover is used beforehand
  public Expression<?> visit(LetExpression let, Void data) {
    Expression result = let.flattenLetExpression();
    return visit(result, data);
  }

  public <T> Expression<T> apply(Expression<T> expr, Void data) {
    return visit(expr, data).requireAs(expr.getType());
  }
}
