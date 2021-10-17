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

// should be used after removal of equivalences, implications, ifThenElse and XOR
// negations should be handled ahead of ConjunctionCreator
public class ConjunctionCreatorVisitor extends DuplicatingVisitor<Void> {

  private static final ConjunctionCreatorVisitor INSTANCE = new ConjunctionCreatorVisitor();

  public static ConjunctionCreatorVisitor getInstance() {
    return INSTANCE;
  }

  int countCNFSteps;

  // helper to reduce recursion
  public Expression<?> pushDisjunction(Expression expr) {
    if (!(expr instanceof PropositionalCompound)) {
      return expr;
    }
    Expression<Boolean> leftChild = ((PropositionalCompound) expr).getLeft();
    Expression<Boolean> rightChild = ((PropositionalCompound) expr).getRight();
    LogicalOperator operator = ((PropositionalCompound) expr).getOperator();

    boolean operatorIsOR = operator.equals(LogicalOperator.OR);
    boolean operatorIsAND = operator.equals(LogicalOperator.AND);
    boolean leftIsPropComp = leftChild instanceof PropositionalCompound;
    boolean rightIsPropComp = rightChild instanceof PropositionalCompound;
    if (operatorIsAND) {
      return expr;
    }
    if (operatorIsOR && leftIsPropComp && rightIsPropComp) {
      boolean leftOpIsOR =
          ((PropositionalCompound) leftChild).getOperator().equals(LogicalOperator.OR);
      boolean leftOpIsAND =
          ((PropositionalCompound) leftChild).getOperator().equals(LogicalOperator.AND);
      boolean rightOpIsOR =
          ((PropositionalCompound) rightChild).getOperator().equals(LogicalOperator.OR);
      boolean rightOpIsAND =
          ((PropositionalCompound) rightChild).getOperator().equals(LogicalOperator.AND);

      Expression<Boolean> leftLeft = ((PropositionalCompound) leftChild).getLeft();
      Expression<Boolean> leftRight = ((PropositionalCompound) leftChild).getRight();
      Expression<Boolean> rightLeft = ((PropositionalCompound) rightChild).getLeft();
      Expression<Boolean> rightRight = ((PropositionalCompound) rightChild).getRight();

      if (leftOpIsAND && rightOpIsAND) {
        // case: (A AND B) OR (C AND D)
        countCNFSteps++;
        return PropositionalCompound.create(
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushDisjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(leftLeft, LogicalOperator.OR, rightLeft))),
                LogicalOperator.AND,
                pushDisjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftLeft, LogicalOperator.OR, rightRight)))),
            LogicalOperator.AND,
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushDisjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftRight, LogicalOperator.OR, rightLeft))),
                LogicalOperator.AND,
                pushDisjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftRight, LogicalOperator.OR, rightRight)))));

      } else if (leftOpIsAND && rightOpIsOR) {
        // case: (A AND B) OR (C OR D)
        countCNFSteps++;
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushDisjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftLeft, LogicalOperator.OR, rightChild))),
                LogicalOperator.AND,
                pushDisjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftRight, LogicalOperator.OR, rightChild))));
        return result;

      } else if (leftOpIsOR && rightOpIsAND) {
        // case: (A OR B) OR (C AND D)
        countCNFSteps++;
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushDisjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftChild, LogicalOperator.OR, rightLeft))),
                LogicalOperator.AND,
                pushDisjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftChild, LogicalOperator.OR, rightRight))));
        return result;

      } else if (leftOpIsOR && rightOpIsOR) {
        // case: (A OR B) OR (C OR D)
        // don't count this as step as no transformation is performed
        return expr;
      }
    } else if (leftIsPropComp && !rightIsPropComp) {
      boolean leftOpIsOR =
          ((PropositionalCompound) leftChild).getOperator().equals(LogicalOperator.OR);
      boolean leftOpIsAND =
          ((PropositionalCompound) leftChild).getOperator().equals(LogicalOperator.AND);

      Expression leftLeft = ((PropositionalCompound) leftChild).getLeft();
      Expression leftRight = ((PropositionalCompound) leftChild).getRight();

      if (operatorIsOR && leftOpIsAND) {
        // case: (A AND B) OR (C)
        countCNFSteps++;
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushDisjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftLeft, LogicalOperator.OR, rightChild))),
                LogicalOperator.AND,
                pushDisjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftRight, LogicalOperator.OR, rightChild))));
        return result;

      } else if (operatorIsOR && leftOpIsOR) {
        // case: (A OR B) OR (C)
        // don't count this as step as no transformation is performed
        return expr;
      }
    } else if (operatorIsOR && !leftIsPropComp && rightIsPropComp) {
      boolean rightOpIsOR =
          ((PropositionalCompound) rightChild).getOperator().equals(LogicalOperator.OR);
      boolean rightOpIsAND =
          ((PropositionalCompound) rightChild).getOperator().equals(LogicalOperator.AND);

      Expression<Boolean> rightLeft = ((PropositionalCompound) rightChild).getLeft();
      Expression<Boolean> rightRight = ((PropositionalCompound) rightChild).getRight();

      if (rightOpIsAND) {
        // case: (A) OR (C AND D)
        countCNFSteps++;
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushDisjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftChild, LogicalOperator.OR, rightLeft))),
                LogicalOperator.AND,
                pushDisjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftChild, LogicalOperator.OR, rightRight))));
        return result;

      } else if (rightOpIsOR) {
        // case: (A) OR (C OR D)
        // don't count this as step as no transformation is performed
        return expr;
      }
    }
    // if we are here, there are no conjunctions under disjunctions in the tree (anymore)
    Expression<Boolean> result = PropositionalCompound.create(leftChild, operator, rightChild);
    return result;
  }

  @Override
  public Expression<?> visit(PropositionalCompound expr, Void data) {
    Expression leftChild = visit(expr.getLeft());
    Expression rightChild = visit(expr.getRight());
    LogicalOperator operator = expr.getOperator();

    boolean operatorIsOR = operator.equals(LogicalOperator.OR);
    boolean operatorIsAND = operator.equals(LogicalOperator.AND);
    boolean leftIsPropComp = leftChild instanceof PropositionalCompound;
    boolean rightIsPropComp = rightChild instanceof PropositionalCompound;

    if (leftIsPropComp && rightIsPropComp) {
      boolean leftOpIsOR =
          ((PropositionalCompound) leftChild).getOperator().equals(LogicalOperator.OR);
      boolean leftOpIsAND =
          ((PropositionalCompound) leftChild).getOperator().equals(LogicalOperator.AND);
      boolean rightOpIsOR =
          ((PropositionalCompound) rightChild).getOperator().equals(LogicalOperator.OR);
      boolean rightOpIsAND =
          ((PropositionalCompound) rightChild).getOperator().equals(LogicalOperator.AND);

      Expression<Boolean> leftLeft = ((PropositionalCompound) leftChild).getLeft();
      Expression<Boolean> leftRight = ((PropositionalCompound) leftChild).getRight();
      Expression<Boolean> rightLeft = ((PropositionalCompound) rightChild).getLeft();
      Expression<Boolean> rightRight = ((PropositionalCompound) rightChild).getRight();
      // further visits in children are needed to push disjunctions as far as possible
      if (operatorIsOR && leftOpIsAND && rightOpIsAND) {
        // case: (A AND B) OR (C AND D)
        countCNFSteps++;
        Expression result =
            PropositionalCompound.create(
                PropositionalCompound.create(
                    (Expression<Boolean>)
                        pushDisjunction(
                            NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                                PropositionalCompound.create(
                                    leftLeft, LogicalOperator.OR, rightLeft))),
                    LogicalOperator.AND,
                    pushDisjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftLeft, LogicalOperator.OR, rightRight)))),
                LogicalOperator.AND,
                PropositionalCompound.create(
                    (Expression<Boolean>)
                        pushDisjunction(
                            NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                                PropositionalCompound.create(
                                    leftRight, LogicalOperator.OR, rightLeft))),
                    LogicalOperator.AND,
                    pushDisjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftRight, LogicalOperator.OR, rightRight)))));
        return result;

      } else if (operatorIsOR && leftOpIsAND && rightOpIsOR) {
        // case: (A AND B) OR (C OR D)
        countCNFSteps++;
        Expression<Boolean> result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushDisjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftLeft, LogicalOperator.OR, rightChild))),
                LogicalOperator.AND,
                pushDisjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftRight, LogicalOperator.OR, rightChild))));
        return result;

      } else if (operatorIsOR && leftOpIsOR && rightOpIsAND) {
        // case: (A OR B) OR (C AND D)
        countCNFSteps++;
        Expression<Boolean> result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushDisjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftChild, LogicalOperator.OR, rightLeft))),
                LogicalOperator.AND,
                pushDisjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftChild, LogicalOperator.OR, rightRight))));
        return result;

      } else if (operatorIsOR && leftOpIsOR && rightOpIsOR) {
        // case: (A OR B) OR (C OR D)
        // don't count this as step as no transformation is performed
        return expr;
      }

    } else if (leftIsPropComp && !rightIsPropComp) {
      boolean leftOpIsOR =
          ((PropositionalCompound) leftChild).getOperator().equals(LogicalOperator.OR);
      boolean leftOpIsAND =
          ((PropositionalCompound) leftChild).getOperator().equals(LogicalOperator.AND);

      Expression<Boolean> leftLeft = ((PropositionalCompound) leftChild).getLeft();
      Expression<Boolean> leftRight = ((PropositionalCompound) leftChild).getRight();

      if (operatorIsOR && leftOpIsAND) {
        // case: (A AND B) OR (C)
        countCNFSteps++;
        Expression<Boolean> result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushDisjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftLeft, LogicalOperator.OR, rightChild))),
                LogicalOperator.AND,
                pushDisjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftRight, LogicalOperator.OR, rightChild))));
        return result;

      } else if (operatorIsOR && leftOpIsOR) {
        // case: (A OR B) OR (C)
        // don't count this as step as no transformation is performed
        return expr;
      }
    } else if (!leftIsPropComp && rightIsPropComp) {
      boolean rightOpIsOR =
          ((PropositionalCompound) rightChild).getOperator().equals(LogicalOperator.OR);
      boolean rightOpIsAND =
          ((PropositionalCompound) rightChild).getOperator().equals(LogicalOperator.AND);

      Expression<Boolean> rightLeft = ((PropositionalCompound) rightChild).getLeft();
      Expression<Boolean> rightRight = ((PropositionalCompound) rightChild).getRight();

      if (operatorIsOR && rightOpIsAND) {
        // case: (A) OR (C AND D)
        countCNFSteps++;
        Expression<Boolean> result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushDisjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftChild, LogicalOperator.OR, rightLeft))),
                LogicalOperator.AND,
                pushDisjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftChild, LogicalOperator.OR, rightRight))));
        return result;

      } else if (operatorIsOR && rightOpIsOR) {
        // case: (A) OR (C OR D)
        // don't count this as step as no transformation is performed
        return expr;
      }

    } else if (!leftIsPropComp && !rightIsPropComp) {
      // cases: (A) OR (B); (A) AND (B)
      // don't count this as step as no transformation is performed
      if (operatorIsOR || operatorIsAND) {
        return expr;
      }
    } else {
      throw new UnsupportedOperationException(
          "Remove equivalences, implications, ifThenElse, and XOR, and handle negations first.");
    }
    // if we are here, there are no conjunctions under disjunctions in the tree (anymore)
    Expression<Boolean> result = PropositionalCompound.create(leftChild, operator, rightChild);
    return result;
  }

  @Override
  public Expression<?> visit(QuantifierExpression q, Void data) {
    // Quantifiers have to be handled beforehand!
    // Here is no exception thrown because this visitor is used in mini scoping and has to return
    // QuantifierExpressions unchanged
    return q;
  }

  // seems to be needed, as LetExpressions can't be flattened bottom-up
  @Override
  public Expression<?> visit(LetExpression expr, Void data) {
    Expression flattened = expr.flattenLetExpression();
    Expression result = visit(flattened, data);
    return result;
  }

  @Override
  public <E> Expression<?> visit(FunctionExpression<E> f, Void data) {
    return f;
  }

  @Override
  public <E> Expression<?> visit(Variable<E> v, Void data) {
    return v;
  }

  @Override
  public <E> Expression<?> visit(Constant<E> c, Void data) {
    return c;
  }

  @Override
  public Expression<?> visit(Negation n, Void data) {
    return n;
  }

  @Override
  public Expression<?> visit(NumericBooleanExpression n, Void data) {
    return n;
  }

  @Override
  public Expression<?> visit(RegExBooleanExpression n, Void data) {
    return n;
  }

  @Override
  public Expression<?> visit(StringBooleanExpression n, Void data) {
    return n;
  }

  @Override
  public Expression<?> visit(StringIntegerExpression n, Void data) {
    return n;
  }

  @Override
  public Expression<?> visit(StringCompoundExpression n, Void data) {
    return n;
  }

  @Override
  public Expression<?> visit(RegexCompoundExpression n, Void data) {
    return n;
  }

  @Override
  public Expression<?> visit(RegexOperatorExpression n, Void data) {
    return n;
  }

  @Override
  public <F, E> Expression<?> visit(CastExpression<F, E> cast, Void data) {
    return cast;
  }

  @Override
  public <E> Expression<?> visit(NumericCompound<E> n, Void data) {
    return n;
  }

  @Override
  public <E> Expression<?> visit(UnaryMinus<E> n, Void data) {
    return n;
  }

  @Override
  public <E> Expression<?> visit(BitvectorExpression<E> bv, Void data) {
    return bv;
  }

  @Override
  public <E> Expression<?> visit(BitvectorNegation<E> n, Void data) {
    return n;
  }

  public <T> Expression<T> apply(Expression<T> expr, Void data) {
    return visit(expr, data).requireAs(expr.getType());
  }

  // this method can be used alternately to the method
  // NormalizationUtil.removeDuplicatesInSameOperatorSequences
  public Expression eliminateNeighborDuplicates(Expression expr) {
    if (!(expr instanceof PropositionalCompound)) {
      return expr;
    } else {
      if (!((PropositionalCompound) expr).getOperator().equals(LogicalOperator.OR)) {
        return expr;
      } else {
        if (((PropositionalCompound) expr)
            .getLeft()
            .equals(((PropositionalCompound) expr).getRight())) {
          return ((PropositionalCompound) expr).getLeft();
        } else {
          return expr;
        }
      }
    }
  }

  public int countCNFSteps(Expression expr) {
    apply(expr, null);
    return countCNFSteps;
  }
}
