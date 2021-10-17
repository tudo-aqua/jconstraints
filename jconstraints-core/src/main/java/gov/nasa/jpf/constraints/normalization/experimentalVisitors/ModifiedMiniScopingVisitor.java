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
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.normalization.NormalizationUtil;
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;
import java.util.ArrayList;
import java.util.List;

// Creation of an anti prenex form (scope of Quantifiers should be minimized)
// Experimental version: no distribution over disjunctions in case of existential quantifiers
// Quantifiers have to be handled ahead of ConjunctionCreator
public class ModifiedMiniScopingVisitor extends DuplicatingVisitor<Void> {

  private static final ModifiedMiniScopingVisitor INSTANCE = new ModifiedMiniScopingVisitor();

  public static ModifiedMiniScopingVisitor getInstance() {
    return INSTANCE;
  }

  @Override
  public Expression<?> visit(QuantifierExpression q, Void data) {
    Quantifier quantifier = q.getQuantifier();
    List<? extends Variable> bound = q.getBoundVariables();
    Expression body = visit(q.getBody(), data);
    // if quantified body is not a Propositional Compound, mini scoping is done here
    // negations have to be pushed beforehand!
    if (!(body instanceof PropositionalCompound)) {
      return q;
    }
    // if we are here, body is a Propositional Compound and there is a possibility of a smaller
    // scope
    Expression leftChild = ((PropositionalCompound) body).getLeft();
    Expression rightChild = ((PropositionalCompound) body).getRight();
    LogicalOperator operator = ((PropositionalCompound) body).getOperator();

    // check if bound variables are only in one child of Propositional Compound
    ArrayList<Variable> freeLeft = new ArrayList<>();
    leftChild.collectFreeVariables(freeLeft);
    boolean boundInFreeLeft = false;

    ArrayList<Variable> freeRight = new ArrayList<>();
    rightChild.collectFreeVariables(freeRight);
    boolean boundInFreeRight = false;

    if (freeLeft != null) {
      for (Variable v : bound) {
        for (Variable f : freeLeft) {
          if (f.equals(v)) {
            boundInFreeLeft = true;
          }
        }
      }
    }

    if (freeRight != null) {
      for (Variable v : bound) {
        for (Variable f : freeRight) {
          if (f.equals(v)) {
            boundInFreeRight = true;
          }
        }
      }
    }

    if (!boundInFreeLeft && boundInFreeRight) {
      // no bound variables in left child of the Propositional Compound
      Expression newLeft = visit(leftChild, data);
      Expression newRight =
          visit(
              QuantifierExpression.create(
                  quantifier, (List<? extends Variable<?>>) bound, rightChild),
              data);
      return PropositionalCompound.create(newLeft, operator, newRight);

    } else if (boundInFreeLeft && !boundInFreeRight) {
      // no bound variables in right child of the Propositional Compound
      Expression newLeft =
          visit(
              QuantifierExpression.create(
                  quantifier, (List<? extends Variable<?>>) bound, leftChild),
              data);
      Expression newRight = visit(rightChild, data);
      return PropositionalCompound.create(newLeft, operator, newRight);

    } else if (boundInFreeLeft && boundInFreeRight) {
      // both children of Propositional Compound contain bound variables
      if (quantifier == Quantifier.FORALL) {
        if (operator == LogicalOperator.AND) {
          // quantifier can be pushed into the subformulas
          Expression newLeft =
              visit(
                  QuantifierExpression.create(
                      quantifier, (List<? extends Variable<?>>) bound, leftChild),
                  data);
          Expression newRight =
              visit(
                  QuantifierExpression.create(
                      quantifier, (List<? extends Variable<?>>) bound, rightChild),
                  data);
          return PropositionalCompound.create(newLeft, operator, newRight);
        }
        if (operator == LogicalOperator.OR) {
          // FORALL is blocked by OR: try to transform body to CNF and visit again
          Expression result = NormalizationUtil.createCNFNoQuantorHandling(body);
          if (result instanceof PropositionalCompound) {
            LogicalOperator newOperator = ((PropositionalCompound) result).getOperator();
            if (newOperator == LogicalOperator.AND) {
              return visit(
                  QuantifierExpression.create(
                      quantifier, (List<? extends Variable<?>>) bound, result));
            }
          }
        }
      }
      if (quantifier == Quantifier.EXISTS) {
        // Experimental version: Nonnengart et al. suggest not to distribute over disjunctions
        // "in order to avoid generating unnecessarily many Skolem functions"
        if (operator == LogicalOperator.OR) {
          // quantifier can be pushed into the subformulas
          Expression newLeft =
              visit(
                  QuantifierExpression.create(
                      quantifier, (List<? extends Variable<?>>) bound, leftChild),
                  data);
          Expression newRight =
              visit(
                  QuantifierExpression.create(
                      quantifier, (List<? extends Variable<?>>) bound, rightChild),
                  data);
          return PropositionalCompound.create(newLeft, operator, newRight);
        }
        if (operator == LogicalOperator.AND) {
          // EXISTS is blocked by AND; no transformation in this experimental version
          return q;
        }
      }
    }
    // no bound variables in children
    return q;
  }

  public <T> Expression<T> apply(Expression<T> expr, Void data) {
    return visit(expr, data).requireAs(expr.getType());
  }
}
