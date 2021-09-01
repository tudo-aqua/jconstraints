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
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;

//this visitor should ensure the ordering: Variable/Compound (operator/comparator) Constant
public class OrderingVisitor extends
    DuplicatingVisitor<Void> {

  private static final OrderingVisitor INSTANCE = new OrderingVisitor();

  public static OrderingVisitor getInstance(){
    return INSTANCE;
  }

  @Override
  public Expression<?> visit(NumericBooleanExpression n, Void data) {
    Expression left = visit(n.getLeft(), data);
    Expression right = visit(n.getRight(), data);
    NumericComparator comparator = n.getComparator();

    if (left instanceof UnaryMinus && !(right instanceof Constant)){
      if (((UnaryMinus<?>) left).getNegated() instanceof Constant){
        if (comparator.equals(NumericComparator.LT)){
          return NumericBooleanExpression.create(right, NumericComparator.GT, left);
        } else if (comparator.equals(NumericComparator.LE)){
          return NumericBooleanExpression.create(right, NumericComparator.GE, left);
        } else if (comparator.equals(NumericComparator.GT)){
          return NumericBooleanExpression.create(right, NumericComparator.LT, left);
        } else if (comparator.equals(NumericComparator.GE)){
          return NumericBooleanExpression.create(right, NumericComparator.LE, left);
        } else {
          //EQ and NE should not be changed
          return NumericBooleanExpression.create(right, comparator, left);
        }
      }
    }
    if (left instanceof Negation && !(right instanceof Constant)) {
      if (!(((Negation) left).getNegated() instanceof Variable) && !(((Negation) left).getNegated() instanceof FunctionExpression)){
        if (comparator.equals(NumericComparator.LT)){
          return NumericBooleanExpression.create(right, NumericComparator.GT, left);
        } else if (comparator.equals(NumericComparator.LE)){
          return NumericBooleanExpression.create(right, NumericComparator.GE, left);
        } else if (comparator.equals(NumericComparator.GT)){
          return NumericBooleanExpression.create(right, NumericComparator.LT, left);
        } else if (comparator.equals(NumericComparator.GE)){
          return NumericBooleanExpression.create(right, NumericComparator.LE, left);
        } else {
          //EQ and NE should not be changed
          return NumericBooleanExpression.create(right, comparator, left);
        }
      }
    }

    if ((left instanceof Constant && !(right instanceof Constant)) ||
        ((!(left instanceof Variable) && !(left instanceof FunctionExpression)) && (right instanceof Variable || right instanceof FunctionExpression))){
      if (comparator.equals(NumericComparator.LT)){
        return NumericBooleanExpression.create(right, NumericComparator.GT, left);
      } else if (comparator.equals(NumericComparator.LE)){
        return NumericBooleanExpression.create(right, NumericComparator.GE, left);
      } else if (comparator.equals(NumericComparator.GT)){
        return NumericBooleanExpression.create(right, NumericComparator.LT, left);
      } else if (comparator.equals(NumericComparator.GE)){
        return NumericBooleanExpression.create(right, NumericComparator.LE, left);
      } else {
        //EQ and NE should not be changed
        return NumericBooleanExpression.create(right, comparator, left);
      }
    }
    return NumericBooleanExpression.create(left, comparator, right);
  }

  @Override
  public <E> Expression<?> visit(NumericCompound<E> n, Void data) {
    Expression left = visit(n.getLeft(), data);
    Expression right = visit(n.getRight(), data);
    NumericOperator operator = n.getOperator();

    if (left instanceof UnaryMinus && !(right instanceof Constant)){
      if (((UnaryMinus<?>) left).getNegated() instanceof Constant) {
        if (operator.equals(NumericOperator.PLUS) || operator.equals(NumericOperator.MUL)) {
          //no change of order if NumericOperator is Minus, REM, MOD or DIV (transformation here more complex)
          return NumericCompound.create(right, operator, left);
        }
      }
    }

    if (left instanceof Constant && !(right instanceof Constant)){
      if(operator.equals(NumericOperator.PLUS) || operator.equals(NumericOperator.MUL)){
        //no change of order if NumericOperator is Minus, REM, MOD or DIV (transformation here more complex)
        return NumericCompound.create(right, operator, left);
      }
    }
    return NumericCompound.create(left, operator, right);
  }

  @Override
  public Expression<?> visit(PropositionalCompound n, Void data) {
    Expression left = visit(n.getLeft(), data);
    Expression right = visit(n.getRight(), data);
    LogicalOperator operator = n.getOperator();
    if (operator.equals(LogicalOperator.IMPLY)){
      return PropositionalCompound.create(left, operator, right);
    }
    if (left instanceof  QuantifierExpression && !(right instanceof QuantifierExpression)){
      return PropositionalCompound.create(right, operator, left);
    }
    if (left instanceof Negation) {
      if (((Negation) left).getNegated() instanceof Constant && !(right instanceof Constant)){
        return PropositionalCompound.create(right, operator, left);
      } else if (((((Negation) left).getNegated() instanceof Variable) || (((Negation) left).getNegated() instanceof FunctionExpression))  && ((right instanceof Variable) || (right instanceof FunctionExpression))){
        return PropositionalCompound.create(right, operator, left);
      } else {
        return PropositionalCompound.create(left, operator, right);
      }
    }
    if ((left instanceof Constant && !(right instanceof Constant))
        || ((!(left instanceof Variable) && !(left instanceof FunctionExpression)) && (right instanceof Variable || right instanceof FunctionExpression))) {
      return PropositionalCompound.create(right, operator, left);
    } else if (left instanceof PropositionalCompound && right instanceof PropositionalCompound) {
      if (NormalizationUtil.checkIfSameOperator(n)){
        if (!(NormalizationUtil.checkIfOnlyLiterals(left)) && NormalizationUtil.checkIfOnlyLiterals(right)){
          //right child contains only Variables, Constants, FunctionExpressions or Negations (of Var, Const, Func)
          return PropositionalCompound.create(right, operator, left);
        } else if (!(NormalizationUtil.checkIfOnlyLiterals(((PropositionalCompound) left).getRight())) && NormalizationUtil.checkIfOnlyLiterals(((PropositionalCompound) right).getLeft())){
          //left part of right child contains only Variables, Constants, FunctionExpressions or Negations (of Var, Const, Func)
          return PropositionalCompound.create(
              PropositionalCompound.create(((PropositionalCompound) left).getLeft(), operator, ((PropositionalCompound) right).getLeft()),
              operator,
              PropositionalCompound.create(((PropositionalCompound) left).getRight(), operator, ((PropositionalCompound) right).getRight()));
        }
      }
    } else if (!(left instanceof Variable) && !(left instanceof FunctionExpression) && right instanceof Negation) {
      if (((Negation) right).getNegated() instanceof Variable || ((Negation) right).getNegated() instanceof FunctionExpression){
        return PropositionalCompound.create(right, operator, left);
      } else {
        return PropositionalCompound.create(left, operator, right);
      }
    }
    return PropositionalCompound.create(left, operator, right);
  }

  @Override
  public Expression<?> visit(Negation n, Void data) {
    return n;
  }

  @Override
  public <E> Expression<?> visit(UnaryMinus<E> n, Void data) {
    return n;
  }

  @Override
  public Expression<?> visit(QuantifierExpression q, Void data) {
    return QuantifierExpression.create(q.getQuantifier(), q.getBoundVariables(), (Expression<Boolean>) visit(q.getBody(), data));
  }

  @Override
  //Not needed if LetExpressionRemover is used beforehand
  public Expression<?> visit(LetExpression let, Void data) {
    return visit(let.flattenLetExpression(), data);
  }

  public <T> Expression<T> apply(Expression<T> expr, Void data) {
    return visit(expr, data).requireAs(expr.getType());
  }
}
