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
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorNegation;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
import gov.nasa.jpf.constraints.expressions.RegexCompoundExpression;
import gov.nasa.jpf.constraints.expressions.RegexOperatorExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringCompoundExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;

// should be used after removal of equivalences, implications, ifThenElses and XOR
// negations should be handled ahead of DisjunctionCreator
public class DisjunctionCreatorVisitor extends DuplicatingVisitor<Void> {

  private static final DisjunctionCreatorVisitor INSTANCE = new DisjunctionCreatorVisitor();

  public static DisjunctionCreatorVisitor getInstance() {
    return INSTANCE;
  }

  int countDNFSteps;

  // helper to reduce recursion
  public Expression<?> pushConjunction(Expression expr) {
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
    if (operatorIsOR) {
      return expr;
    }
    if (operatorIsAND && leftIsPropComp && rightIsPropComp) {
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

      if (operatorIsAND && leftOpIsOR && rightOpIsOR) {
        // case: (A OR B) AND (C OR D)
        countDNFSteps++;
        Expression result =
            PropositionalCompound.create(
                PropositionalCompound.create(
                    (Expression<Boolean>)
                        pushConjunction(
                            NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                                PropositionalCompound.create(
                                    leftLeft, LogicalOperator.AND, rightLeft))),
                    LogicalOperator.OR,
                    pushConjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftLeft, LogicalOperator.AND, rightRight)))),
                LogicalOperator.OR,
                PropositionalCompound.create(
                    (Expression<Boolean>)
                        pushConjunction(
                            NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                                PropositionalCompound.create(
                                    leftRight, LogicalOperator.AND, rightLeft))),
                    LogicalOperator.OR,
                    pushConjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftRight, LogicalOperator.AND, rightRight)))));
        return result;

      } else if (operatorIsAND && leftOpIsOR && rightOpIsAND) {
        // case: (A OR B) AND (C AND D)
        countDNFSteps++;
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushConjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftLeft, LogicalOperator.AND, rightChild))),
                LogicalOperator.OR,
                pushConjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftRight, LogicalOperator.AND, rightChild))));
        return result;

      } else if (operatorIsAND && leftOpIsAND && rightOpIsOR) {
        // case: (A AND B) AND (C OR D)
        countDNFSteps++;
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushConjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftChild, LogicalOperator.AND, rightLeft))),
                LogicalOperator.OR,
                pushConjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftChild, LogicalOperator.AND, rightRight))));
        return result;

      } else if (operatorIsAND && leftOpIsAND && rightOpIsAND) {
        // case: (A AND B) AND (C AND D)
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

      if (operatorIsAND && leftOpIsOR) {
        // case: (A OR B) AND (C)
        countDNFSteps++;
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushConjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftLeft, LogicalOperator.AND, rightChild))),
                LogicalOperator.OR,
                pushConjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftRight, LogicalOperator.AND, rightChild))));
        return result;

      } else if (operatorIsAND && leftOpIsAND) {
        // case: (A AND B) AND (C)
        // don't count this as step as no transformation is performed
        return expr;
      }
    } else if (!leftIsPropComp && rightIsPropComp) {
      boolean rightOpIsOR =
          ((PropositionalCompound) rightChild).getOperator().equals(LogicalOperator.OR);
      boolean rightOpIsAND =
          ((PropositionalCompound) rightChild).getOperator().equals(LogicalOperator.AND);

      Expression rightLeft = ((PropositionalCompound) rightChild).getLeft();
      Expression rightRight = ((PropositionalCompound) rightChild).getRight();

      if (operatorIsAND && rightOpIsOR) {
        // case: (A) AND (C OR D)
        countDNFSteps++;
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushConjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftChild, LogicalOperator.AND, rightLeft))),
                LogicalOperator.OR,
                pushConjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftChild, LogicalOperator.AND, rightRight))));
        return result;

      } else if (operatorIsAND && rightOpIsAND) {
        // case: (A) AND (C AND D)
        // don't count this as step as no transformation is performed
        return expr;
      }

    } else if (!leftIsPropComp && !rightIsPropComp) {
      // cases: (A) AND (B); (A) OR (B)
      // don't count this as step as no transformation is performed
      if (operatorIsOR || operatorIsAND) {
        return expr;
      }
    }
    // if we are here, there are no disjunctions under conjunctions in the tree (anymore)
    Expression result = PropositionalCompound.create(leftChild, operator, rightChild);
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

      Expression leftLeft = ((PropositionalCompound) leftChild).getLeft();
      Expression leftRight = ((PropositionalCompound) leftChild).getRight();
      Expression rightLeft = ((PropositionalCompound) rightChild).getLeft();
      Expression rightRight = ((PropositionalCompound) rightChild).getRight();
      // further visits in children are needed to push conjunctions as far as possible
      if (operatorIsAND && leftOpIsOR && rightOpIsOR) {
        // case: (A OR B) AND (C OR D)
        countDNFSteps++;
        Expression result =
            PropositionalCompound.create(
                PropositionalCompound.create(
                    (Expression<Boolean>)
                        pushConjunction(
                            NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                                PropositionalCompound.create(
                                    leftLeft, LogicalOperator.AND, rightLeft))),
                    LogicalOperator.OR,
                    pushConjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftLeft, LogicalOperator.AND, rightRight)))),
                LogicalOperator.OR,
                PropositionalCompound.create(
                    (Expression<Boolean>)
                        pushConjunction(
                            NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                                PropositionalCompound.create(
                                    leftRight, LogicalOperator.AND, rightLeft))),
                    LogicalOperator.OR,
                    pushConjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftRight, LogicalOperator.AND, rightRight)))));
        return result;

      } else if (operatorIsAND && leftOpIsOR && rightOpIsAND) {
        // case: (A OR B) AND (C AND D)
        countDNFSteps++;
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushConjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftLeft, LogicalOperator.AND, rightChild))),
                LogicalOperator.OR,
                pushConjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftRight, LogicalOperator.AND, rightChild))));
        return result;

      } else if (operatorIsAND && leftOpIsAND && rightOpIsOR) {
        // case: (A AND B) AND (C OR D)
        countDNFSteps++;
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushConjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftChild, LogicalOperator.AND, rightLeft))),
                LogicalOperator.OR,
                pushConjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftChild, LogicalOperator.AND, rightRight))));
        return result;

      } else if (operatorIsAND && leftOpIsAND && rightOpIsAND) {
        // case: (A AND B) AND (C AND D)
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

      if (operatorIsAND && leftOpIsOR) {
        // case: (A OR B) AND (C)
        countDNFSteps++;
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushConjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftLeft, LogicalOperator.AND, rightChild))),
                LogicalOperator.OR,
                pushConjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftRight, LogicalOperator.AND, rightChild))));
        return result;

      } else if (operatorIsAND && leftOpIsAND) {
        // case: (A AND B) AND (C)
        // don't count this as step as no transformation is performed
        return expr;
      }
    } else if (!leftIsPropComp && rightIsPropComp) {
      boolean rightOpIsOR =
          ((PropositionalCompound) rightChild).getOperator().equals(LogicalOperator.OR);
      boolean rightOpIsAND =
          ((PropositionalCompound) rightChild).getOperator().equals(LogicalOperator.AND);

      Expression rightLeft = ((PropositionalCompound) rightChild).getLeft();
      Expression rightRight = ((PropositionalCompound) rightChild).getRight();

      if (operatorIsAND && rightOpIsOR) {
        // case: (A) AND (C OR D)
        countDNFSteps++;
        Expression result =
            PropositionalCompound.create(
                (Expression<Boolean>)
                    pushConjunction(
                        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                            PropositionalCompound.create(
                                leftChild, LogicalOperator.AND, rightLeft))),
                LogicalOperator.OR,
                pushConjunction(
                    NormalizationUtil.removeDuplicatesInSameOperatorSequences(
                        PropositionalCompound.create(leftChild, LogicalOperator.AND, rightRight))));
        return result;

      } else if (operatorIsAND && rightOpIsAND) {
        // case: (A) AND (C AND D)
        // don't count this as step as no transformation is performed
        return expr;
      }

    } else if (!leftIsPropComp && !rightIsPropComp) {
      // cases: (A) AND (B); (A) OR (B)
      // don't count this as step as no transformation is performed
      if (operatorIsOR || operatorIsAND) {
        return expr;
      }
    } else {
      throw new UnsupportedOperationException(
          "Remove equivalences, implications, ifThenElse, and XOR, and handle negations first.");
    }
    // if we are here, there are no disjunctions under conjunctions in the tree (anymore)
    Expression result =
        NormalizationUtil.removeDuplicatesInSameOperatorSequences(
            PropositionalCompound.create(leftChild, operator, rightChild));
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
    return super.visit(f, data);
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
      if (!((PropositionalCompound) expr).getOperator().equals(LogicalOperator.AND)) {
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

  public int countDNFSteps(Expression expr) {
    apply(expr, null);
    return countDNFSteps;
  }
}
