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
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanOperator;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;
import java.util.List;

// Experimental version: negations are not pushed into logic
public class ModifiedNegatingVisitor extends DuplicatingVisitor<Boolean> {

  private static final ModifiedNegatingVisitor INSTANCE = new ModifiedNegatingVisitor();

  public static ModifiedNegatingVisitor getInstance() {
    return INSTANCE;
  }

  int countLogicalNegations = 0;
  int countAllNegationPushs = 0;

  @Override
  public Expression<?> visit(NumericBooleanExpression expr, Boolean shouldNegate) {
    // modification for checking the impact of pushing negations completely into logic
    if (shouldNegate) {
      return Negation.create(expr);
    }
    return expr;
  }

  @Override
  public Expression<?> visit(PropositionalCompound expr, Boolean shouldNegate) {
    // if shouldNegate is true, a Negation is visited
    if (shouldNegate) {
      Expression<Boolean> left = expr.getLeft();
      Expression<Boolean> right = expr.getRight();
      LogicalOperator operator = expr.getOperator();
      LogicalOperator negOperator = operator.invert();
      Expression<Boolean> newLeft = left;
      Expression<Boolean> newRight = right;

      // if an equivalence or an xor is negated, only the operator is inverted
      // otherwise not only the operator has to be inverted but also the children have to bei
      // negated
      if (operator.equals(LogicalOperator.EQUIV) || operator.equals(LogicalOperator.XOR)) {
        newLeft = (Expression<Boolean>) visit(left, false);
        newRight = (Expression<Boolean>) visit(right, false);
      } else {
        if (left.getType().equals(BuiltinTypes.BOOL)) {
          newLeft = (Expression<Boolean>) visit(Negation.create(left), false);
        } else {
          newLeft = (Expression<Boolean>) visit(left, false);
        }
        if (right.getType().equals(BuiltinTypes.BOOL)) {
          newRight = (Expression<Boolean>) visit(Negation.create(right), false);
        } else {
          newRight = (Expression<Boolean>) visit(right, false);
        }
      }

      countLogicalNegations++;
      countAllNegationPushs++;
      return PropositionalCompound.create(newLeft, negOperator, newRight);

    } else {
      Expression<Boolean> left = (Expression<Boolean>) visit(expr.getLeft(), false);
      Expression<Boolean> right = (Expression<Boolean>) visit(expr.getRight(), false);
      LogicalOperator operator = expr.getOperator();
      return PropositionalCompound.create(left, operator, right);
    }
  }

  @Override
  public Expression<?> visit(Negation expr, Boolean shouldNegate) {
    if (shouldNegate) {
      countAllNegationPushs++;
      // negation of a negation
      if (expr.getType().equals(BuiltinTypes.BOOL)) {
        return visit(expr.getNegated(), false);
      } else {
        // should be unnecessary as a Negation should always be boolean typed
        return expr;
      }
    } else {
      if (expr.getType().equals(BuiltinTypes.BOOL)) {
        return visit(expr.getNegated(), true);
      } else {
        return expr;
      }
    }
  }

  @Override
  public Expression visit(Variable var, Boolean shouldNegate) {

    if (shouldNegate) {
      if (var.getType().equals(BuiltinTypes.BOOL)) {
        countAllNegationPushs++;
        Negation negated = Negation.create(var);
        return negated;
      }
    }
    return var;
  }

  public Expression<?> visit(QuantifierExpression quantified, Boolean shouldNegate) {
    Quantifier q = quantified.getQuantifier();
    List<? extends Variable<?>> vars = quantified.getBoundVariables();
    Expression<Boolean> body = quantified.getBody();

    if (shouldNegate) {
      countAllNegationPushs++;
      QuantifierExpression qExpr =
          QuantifierExpression.create(
              q.negate(), vars, (Expression<Boolean>) visit(Negation.create(body), false));
      return qExpr;
    }
    Expression expr =
        QuantifierExpression.create(q, vars, (Expression<Boolean>) visit(body, false));
    return expr;
  }

  @Override
  public Expression<?> visit(StringBooleanExpression expr, Boolean shouldNegate) {
    if (shouldNegate) {
      countAllNegationPushs++;
      StringBooleanOperator operator = expr.getOperator();
      Expression<?> left = expr.getLeft();
      Expression<?> right = expr.getRight();

      if (operator.equals(StringBooleanOperator.EQUALS)) {
        return StringBooleanExpression.createNotEquals(left, right);
      } else if (operator.equals(StringBooleanOperator.NOTEQUALS)) {
        return StringBooleanExpression.createEquals(left, right);
      } else {
        // other negations of operators not implemented
        return Negation.create(expr);
      }
    }
    return expr;
  }

  public <E> Expression<?> visit(IfThenElse<E> expr, Boolean shouldNegate) {
    Expression thenExpr = expr.getThen();
    Expression elseExpr = expr.getElse();
    if (shouldNegate) {
      countAllNegationPushs++;
      if (thenExpr.getType().equals(BuiltinTypes.BOOL)
          && elseExpr.getType().equals(BuiltinTypes.BOOL)) {
        Expression firstPart =
            PropositionalCompound.create(
                Negation.create(expr.getIf()), LogicalOperator.OR, thenExpr);
        Expression secondPart =
            PropositionalCompound.create(expr.getIf(), LogicalOperator.OR, elseExpr);

        // visit again for finding nested IfThenElse
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>) firstPart, LogicalOperator.AND, secondPart);

        return visit(Negation.create(result), false);
      } else {
        // if IfThenElse from NumericBooleanExpression or NumericCompound reach up to here, they
        // should not be negated
        return expr;
      }
    }

    if (thenExpr.getType().equals(BuiltinTypes.BOOL)
        && elseExpr.getType().equals(BuiltinTypes.BOOL)) {
      Expression firstPart =
          PropositionalCompound.create(Negation.create(expr.getIf()), LogicalOperator.OR, thenExpr);
      Expression secondPart =
          PropositionalCompound.create(expr.getIf(), LogicalOperator.OR, elseExpr);

      // visit again for finding nested IfThenElse
      Expression result =
          PropositionalCompound.create(
              (Expression<Boolean>) visit(firstPart, false),
              LogicalOperator.AND,
              visit(secondPart, false));

      return result;
    }
    return visit(expr, false);
  }

  @Override
  public <E> Expression<?> visit(FunctionExpression<E> expr, Boolean shouldNegate) {
    // FunctionExpressions are not further negated
    if (shouldNegate) {
      countAllNegationPushs++;
      return Negation.create((Expression<Boolean>) expr);
    }
    return expr;
  }

  @Override
  public Expression<?> visit(RegExBooleanExpression expr, Boolean shouldNegate) {
    if (shouldNegate) {
      countAllNegationPushs++;
      return Negation.create(expr);
    }
    return expr;
  }

  @Override
  public <E> Expression<?> visit(Constant<E> c, Boolean shouldNegate) {
    if (shouldNegate) {
      if (c.getType().equals(BuiltinTypes.BOOL)) {
        countAllNegationPushs++;
        return Negation.create((Expression<Boolean>) c);
      }
    }
    return c;
  }

  @Override
  public <E> Expression<?> visit(UnaryMinus<E> expr, Boolean shouldNegate) {
    if (shouldNegate) {
      if (expr.getType().equals(BuiltinTypes.BOOL)) {
        countAllNegationPushs++;
        return expr.getNegated();
      }
    }
    return expr;
  }

  @Override
  public <E> Expression<?> visit(BitvectorExpression<E> expr, Boolean shouldNegate) {
    if (shouldNegate) {
      countAllNegationPushs++;
      Expression left = expr.getLeft();
      Expression right = expr.getRight();
      BitvectorOperator operator = expr.getOperator();

      if (operator.equals(BitvectorOperator.AND)) {
        return BitvectorExpression.create(left, BitvectorOperator.OR, right);
      } else if (operator.equals(BitvectorOperator.OR)) {
        return BitvectorExpression.create(left, BitvectorOperator.AND, right);
      }
      return expr;
    }
    return expr;
  }

  @Override
  // should be unnecessary after the LetExpressionRemover
  public Expression<?> visit(LetExpression expr, Boolean shouldNegate) {
    Expression flattened = expr.flattenLetExpression();
    if (shouldNegate) {
      countAllNegationPushs++;
      if (flattened.getType().equals(BuiltinTypes.BOOL)) {
        return visit(Negation.create(flattened), false);
      }
    }
    return visit(flattened, false);
  }

  @Override
  public <E> Expression<?> visit(NumericCompound<E> n, Boolean data) {
    return n;
  }
  // defaultVisit for CastExpression, NumericCompound, StringIntegerExpression,
  // StringCompoundExpression, RegexCompoundExpression, RegexOperatorExpression,
  // RegExBooleanExpression, BitvectorNegation
  @Override
  protected <E> Expression<?> defaultVisit(Expression<E> expression, Boolean shouldNegate) {
    return super.defaultVisit(expression, shouldNegate);
  }

  public <T> Expression<T> apply(Expression<T> expr, Boolean shouldNegate) {
    return visit(expr, shouldNegate).requireAs(expr.getType());
  }

  public int[] countNegationSteps(Expression expr) {
    apply(expr, false);
    int[] counter = new int[2];
    counter[0] = countLogicalNegations;
    counter[1] = countAllNegationPushs;
    return counter;
  }
}
