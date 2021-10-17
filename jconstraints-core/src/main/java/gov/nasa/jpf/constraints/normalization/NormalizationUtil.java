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
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.normalization.analysis.ConjunctionCounterVisitor;
import gov.nasa.jpf.constraints.normalization.analysis.DisjunctionCounterVisitor;
import gov.nasa.jpf.constraints.normalization.analysis.EquivalenceCounterVisitor;
import gov.nasa.jpf.constraints.normalization.analysis.IfThenElseCounterVisitor;
import gov.nasa.jpf.constraints.normalization.analysis.ImplicationCounterVisitor;
import gov.nasa.jpf.constraints.normalization.analysis.MaxIfThenElseDepthVisitor;
import gov.nasa.jpf.constraints.normalization.analysis.NegationCounterVisitor;
import gov.nasa.jpf.constraints.normalization.analysis.QuantifierCounterVisitor;
import gov.nasa.jpf.constraints.normalization.analysis.XORCounterVisitor;
import gov.nasa.jpf.constraints.normalization.experimentalVisitors.CombinedRemoverVisitor;
import gov.nasa.jpf.constraints.normalization.experimentalVisitors.ModifiedIfThenElseRemoverVisitor;
import gov.nasa.jpf.constraints.normalization.experimentalVisitors.ModifiedNegatingVisitor;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

public class NormalizationUtil {

  public static <E> Expression<E> normalize(Expression<E> e, String form) {
    boolean buildCnf = false;
    boolean buildDnf = false;
    if (form.equalsIgnoreCase("cnf")) {
      buildCnf = true;
    } else if (form.equalsIgnoreCase("dnf")) {
      buildDnf = true;
    } else {
      throw new UnsupportedOperationException("Parameter 'cnf' or 'dnf' needed!");
    }

    if (buildCnf) {
      Expression cnf = createCNF(e);
      // alternative without removal of duplicates and ordering:
      // return cnf;
      return orderProblem(
          removeDuplicateSameOperatorSequences(
              removeDuplicatesInSameOperatorSequences(orderProblem(cnf))));
    } else if (buildDnf) {
      Expression dnf = createDNF(e);
      // alternative without removal of duplicates and ordering:
      // return dnf;
      return orderProblem(
          removeDuplicateSameOperatorSequences(
              removeDuplicatesInSameOperatorSequences(orderProblem(dnf))));
    } else {
      throw new UnsupportedOperationException("Parameter 'cnf' or 'dnf' needed!");
    }
  }

  public static <E> Expression<E> createNNF(Expression<E> e) {
    Expression simplified = simplifyProblem(e);

    Expression noIte = eliminateIfThenElse(simplified);
    Expression noEquivalence = eliminateEquivalence(noIte);
    Expression noImplication = eliminateImplication(noEquivalence);
    Expression noXOR = eliminateXOR(noImplication);

    Expression nnf = NegatingVisitor.getInstance().apply(noXOR, false);
    return nnf;
  }

  // experimental method
  public static <E> Expression<E> createNNFNotModularRemovers(Expression<E> e) {
    Expression simplified = simplifyProblem(e);
    Expression noIte = CombinedRemoverVisitor.getInstance().apply(simplified, null);
    Expression nnf = NegatingVisitor.getInstance().apply(noIte, false);
    return nnf;
  }

  public static <E> Expression<E> simpleNegationPush(Expression<E> e) {
    return NegatingVisitor.getInstance().apply(e, false);
  }

  // experimental method
  public static <E> Expression<E> pushNegationModified(Expression<E> e) {
    Expression simplified = simplifyProblem(e);

    Expression noEquivalence = eliminateEquivalence(simplified);
    Expression noImplication = eliminateImplication(noEquivalence);
    Expression noXOR = eliminateXOR(noImplication);
    Expression noIte = eliminateIfThenElse(noXOR);

    Expression nnf = ModifiedNegatingVisitor.getInstance().apply(noIte, false);
    return nnf;
  }

  public static <E> Expression<E> createCNF(Expression<E> e) {
    Expression nnf = createNNF(e);
    if (!nnf.equals(null)) {
      if (quantifierCheck(nnf)) {
        Expression renamed = renameAllBoundVars(nnf);
        // miniscoping is only senseful if there is at least an EXISTS in scope of an FORALL after
        // creation of nnf
        Expression beforeSkolemization;
        if (existsInForall(renamed)) {
          beforeSkolemization = miniScope(renamed);
        } else {
          beforeSkolemization = renamed;
        }
        Expression skolemized = skolemize(beforeSkolemization);
        Expression prenex = prenexing(skolemized);
        if (prenex instanceof QuantifierExpression) {
          Quantifier q = ((QuantifierExpression) prenex).getQuantifier();
          List<? extends Variable<?>> bound = ((QuantifierExpression) prenex).getBoundVariables();
          Expression body = ((QuantifierExpression) prenex).getBody();
          Expression matrix = ConjunctionCreatorVisitor.getInstance().apply(body, null);
          Expression result = QuantifierExpression.create(q, bound, matrix);
          return result;
        } else {
          return ConjunctionCreatorVisitor.getInstance().apply(prenex, null);
        }
      } else {
        return ConjunctionCreatorVisitor.getInstance().apply(nnf, null);
      }
    } else {
      throw new UnsupportedOperationException("Creation of NNF failed, no CNF created!");
    }
  }

  public static <E> Expression<E> createCNFNoQuantorHandling(Expression<E> e) {
    Expression nnf = createNNF(e);
    if (!nnf.equals(null)) {
      return ConjunctionCreatorVisitor.getInstance().apply(nnf, null);
    } else {
      throw new UnsupportedOperationException("Creation of NNF failed, no CNF created!");
    }
  }

  // nnf has to be created beforehand
  public static <E> Expression<E> createDNF(Expression<E> e) {
    Expression nnf = createNNF(e);
    if (!nnf.equals(null)) {
      if (quantifierCheck(nnf)) {
        Expression renamed = renameAllBoundVars(nnf);
        // miniscoping is only senseful if there is at least an EXISTS in scope of an FORALL after
        // creation of nnf
        Expression beforeSkolemization;
        if (existsInForall(renamed)) {
          beforeSkolemization = miniScope(renamed);
        } else {
          beforeSkolemization = renamed;
        }
        Expression skolemized = skolemize(beforeSkolemization);
        Expression prenex = prenexing(skolemized);
        if (prenex instanceof QuantifierExpression) {
          Quantifier q = ((QuantifierExpression) prenex).getQuantifier();
          List<? extends Variable<?>> bound = ((QuantifierExpression) prenex).getBoundVariables();
          Expression<Boolean> body = ((QuantifierExpression) prenex).getBody();
          Expression<Boolean> matrix = DisjunctionCreatorVisitor.getInstance().apply(body, null);
          Expression result = QuantifierExpression.create(q, bound, matrix);
          return result;
        } else {
          return DisjunctionCreatorVisitor.getInstance().apply(prenex, null);
        }
      } else {
        return DisjunctionCreatorVisitor.getInstance().apply(nnf, null);
      }
    } else {
      throw new UnsupportedOperationException("Creation of NNF failed, no DNF created!");
    }
  }

  // nnf has to be created beforehand
  public static <E> Expression<E> createDNFNoQuantorHandling(Expression<E> e) {
    Expression nnf = createNNF(e);
    if (!nnf.equals(null)) {
      return DisjunctionCreatorVisitor.getInstance().apply(nnf, null);
    } else {
      throw new UnsupportedOperationException("Creation of NNF failed, no DNF created!");
    }
  }

  public static <E> Expression<E> simplifyProblem(Expression<E> e) {
    return SimplifyProblemVisitor.getInstance().apply(e, null);
  }

  public static <E> Expression<E> removeDuplicatesInSameOperatorSequences(Expression<E> e) {
    if (e instanceof QuantifierExpression) {
      return (Expression<E>)
          QuantifierExpression.create(
              ((QuantifierExpression) e).getQuantifier(),
              ((QuantifierExpression) e).getBoundVariables(),
              removeDuplicatesInSameOperatorSequences(((QuantifierExpression) e).getBody()));
    }
    if (checkIfSameOperator(e)) {
      LinkedList set = new LinkedList();
      collectExpressionsInSameOperatorSequences(set, e);
      if (e instanceof PropositionalCompound) {
        LogicalOperator operator = ((PropositionalCompound) e).getOperator();
        if (operator.equals(LogicalOperator.OR)) {
          return ExpressionUtil.or(set);
        } else if (operator.equals(LogicalOperator.AND)) {
          return ExpressionUtil.and(set);
        } else {
          throw new UnsupportedOperationException("Remove XOR, IMPLY and EQUIV first");
        }
      }
    } else if (e instanceof PropositionalCompound) {
      Expression<Boolean> left =
          removeDuplicatesInSameOperatorSequences(((PropositionalCompound) e).getLeft());
      Expression<Boolean> right =
          removeDuplicatesInSameOperatorSequences(((PropositionalCompound) e).getRight());
      return (Expression<E>)
          PropositionalCompound.create(left, ((PropositionalCompound) e).getOperator(), right);
    }
    return e;
  }

  public static <E> Expression<E> removeDuplicateSameOperatorSequences(Expression<E> e) {
    if (e instanceof QuantifierExpression) {
      return (Expression<E>)
          QuantifierExpression.create(
              ((QuantifierExpression) e).getQuantifier(),
              ((QuantifierExpression) e).getBoundVariables(),
              removeDuplicateSameOperatorSequences(((QuantifierExpression) e).getBody()));
    }
    if (e instanceof PropositionalCompound) {
      if (!checkIfSameOperator(e)) {
        LinkedList set = new LinkedList();
        collectSameOperatorSequences(set, e);
        LogicalOperator operator = ((PropositionalCompound) e).getOperator();
        if (operator.equals(LogicalOperator.OR)) {
          return ExpressionUtil.or(set);
        } else if (operator.equals(LogicalOperator.AND)) {
          return ExpressionUtil.and(set);
        } else {
          throw new UnsupportedOperationException("Remove XOR, IMPLY and EQUIV first");
        }
      }
    }
    // e is a literal or contains only one "clause" (only one kind of operator)
    return e;
  }

  public static <E> Expression<E> orderProblem(Expression<E> e) {
    return OrderingVisitor.getInstance().apply(e, null);
  }

  public static <E> Expression<E> eliminateEquivalence(Expression<E> e) {
    return EquivalenceRemoverVisitor.getInstance().apply(e, null);
  }

  public static <E> Expression<E> eliminateIfThenElse(Expression<E> e) {
    return IfThenElseRemoverVisitor.getInstance().apply(e, null);
  }

  // experimental method
  public static <E> Expression<E> eliminatePropositionalIfThenElse(Expression<E> e) {
    return ModifiedIfThenElseRemoverVisitor.getInstance().apply(e, null);
  }

  public static <E> Expression<E> eliminateLetExpressions(Expression<E> e) {
    return LetExpressionRemoverVisitor.getInstance().apply(e, null);
  }

  public static <E> Expression<E> eliminateImplication(Expression<E> e) {
    return ImplicationRemoverVisitor.getInstance().apply(e, null);
  }

  public static <E> Expression<E> eliminateXOR(Expression<E> e) {
    return XorRemoverVisitor.getInstance().apply(e, null);
  }

  // Methods for handling of quantifiers
  public static <E> Expression<E> miniScope(Expression<E> e) {
    MiniScopingVisitor m = new MiniScopingVisitor();
    return m.apply(e, null);
  }

  public static <E> Expression<E> renameAllBoundVars(Expression<E> e) {
    HashMap<String, String> data = new HashMap<>();
    RenamingBoundVarVisitor r = new RenamingBoundVarVisitor();
    return r.apply(e, data);
  }

  public static <E> Expression<E> skolemize(Expression<E> e) {
    List<Variable<?>> data = new ArrayList<>();
    SkolemizationVisitor s = new SkolemizationVisitor();
    return s.apply(e, data);
  }

  public static <E> Expression<E> prenexing(Expression<E> e) {
    PrenexFormVisitor p = new PrenexFormVisitor();
    return p.apply(e, null);
  }

  public static Collection<String> collectFunctionNames(Expression<?> expr) {
    Collection<String> functionNames = new ArrayList<>();
    if (expr instanceof FunctionExpression) {
      String name = ((FunctionExpression<?>) expr).getFunction().getName();
      functionNames.add(name);
    }

    Expression<?>[] exprChildren = expr.getChildren();
    for (Expression i : exprChildren) {
      collectFunctionNames(i);
    }
    return functionNames;
  }

  public static boolean nameClashWithExistingFreeVars(
      String name, Collection<Variable<?>> existingVars) {
    if (existingVars != null) {
      for (Variable v : existingVars) {
        String varName = v.getName();
        if (varName.equals(name)) {
          return true;
        }
      }
    }
    return false;
  }

  public static boolean containsDuplicateNames(Collection<Variable<?>> vars) {
    Collection<Variable> existing = new ArrayList<>();
    if (vars != null) {
      for (Variable v : vars) {
        if (existing.contains(v)) {
          return true;
        }
        existing.add(v);
      }
    }
    return false;
  }

  public static boolean checkIfSameOperator(Expression e) {
    if (e instanceof QuantifierExpression) {
      return false;
    }
    if (e instanceof LetExpression) {
      return false;
    }
    if (!(e instanceof PropositionalCompound)) {
      return true;
    } else {
      Expression<Boolean> left = ((PropositionalCompound) e).getLeft();
      Expression<Boolean> right = ((PropositionalCompound) e).getRight();
      LogicalOperator operator = ((PropositionalCompound) e).getOperator();

      if (left instanceof PropositionalCompound && right instanceof PropositionalCompound) {
        if (((PropositionalCompound) left).getOperator().equals(operator)
            && ((PropositionalCompound) right).getOperator().equals(operator)) {
          return (checkIfSameOperator(left) && checkIfSameOperator(right));
        } else {
          return false;
        }
      } else if (left instanceof PropositionalCompound) {
        if (((PropositionalCompound) left).getOperator().equals(operator)) {
          return checkIfSameOperator(left);
        } else {
          return false;
        }
      } else if (right instanceof PropositionalCompound) {
        if (((PropositionalCompound) right).getOperator().equals(operator)) {
          return checkIfSameOperator(right);
        } else {
          return false;
        }
      } else {
        return (checkIfSameOperator(left) && checkIfSameOperator(right));
      }
    }
  }

  // use after checkIfSameOperator()
  public static LinkedList<Expression> collectExpressionsInSameOperatorSequences(
      LinkedList<Expression> clauseSet, Expression e) {
    if (!(e instanceof PropositionalCompound)) {
      if (!clauseSet.contains(e)) {
        clauseSet.add(e);
      }
    } else {
      collectExpressionsInSameOperatorSequences(clauseSet, ((PropositionalCompound) e).getLeft());
      collectExpressionsInSameOperatorSequences(clauseSet, ((PropositionalCompound) e).getRight());
    }
    return clauseSet;
  }

  // can ONLY be used in cnf or dnf!
  // does NOT count clauses, but sequences containing the same operator
  // ((A) AND (B) AND (E)) contains three clauses, but only one same operator sequence
  public static int countSameOperatorSequences(Expression e) {
    if (!checkIfSameOperator(e)) {
      LinkedList<Expression> clauseSet = new LinkedList<>();
      clauseSet = collectSameOperatorSequences(clauseSet, e);
      return clauseSet.size();
    } else {
      // if same operator, we have one clause
      return 1;
    }
  }

  // can ONLY be used in cnf or dnf!
  // so: check operator in methods before using this method
  public static LinkedList<Expression> collectSameOperatorSequences(
      LinkedList<Expression> clauseSet, Expression e) {
    if (e instanceof QuantifierExpression) {
      return collectSameOperatorSequences(clauseSet, ((QuantifierExpression) e).getBody());
    }
    if (e instanceof PropositionalCompound) {
      if (!checkIfSameOperator(e)) {
        boolean sameOperatorLeft = checkIfSameOperator(((PropositionalCompound) e).getLeft());
        boolean sameOperatorRight = checkIfSameOperator(((PropositionalCompound) e).getRight());
        if (sameOperatorLeft && sameOperatorRight) {
          if (!clauseSet.contains(((PropositionalCompound) e).getLeft())) {
            clauseSet.add(((PropositionalCompound) e).getLeft());
          }
          if (!clauseSet.contains(((PropositionalCompound) e).getRight())) {
            clauseSet.add(((PropositionalCompound) e).getRight());
          }
        } else if (!sameOperatorLeft && sameOperatorRight) {
          if (!clauseSet.contains(((PropositionalCompound) e).getRight())) {
            clauseSet.add(((PropositionalCompound) e).getRight());
          }
          collectSameOperatorSequences(clauseSet, ((PropositionalCompound) e).getLeft());
        } else if (sameOperatorLeft && !sameOperatorRight) {
          if (!clauseSet.contains(((PropositionalCompound) e).getLeft())) {
            clauseSet.add(((PropositionalCompound) e).getLeft());
          }
          collectSameOperatorSequences(clauseSet, ((PropositionalCompound) e).getRight());
        } else {
          collectSameOperatorSequences(clauseSet, ((PropositionalCompound) e).getLeft());
          collectSameOperatorSequences(clauseSet, ((PropositionalCompound) e).getRight());
        }
      }
    }
    return clauseSet;
  }

  // check if an PropositionalCompound contains only literals
  public static boolean checkIfOnlyLiterals(Expression e) {
    if (!(e instanceof PropositionalCompound)) {
      if (e instanceof Variable) {
        return true;
      } else if (e instanceof Constant) {
        return true;
      } else if (e instanceof FunctionExpression) {
        return true;
      } else if (e instanceof Negation) {
        Expression neg = ((Negation) e).getNegated();
        return checkIfOnlyLiterals(neg);
      } else {
        return false;
      }
    }
    Expression left = ((PropositionalCompound) e).getLeft();
    Expression right = ((PropositionalCompound) e).getRight();
    return checkIfOnlyLiterals(left) && checkIfOnlyLiterals(right);
  }

  // checking and counting methods
  public static int maxIteDepth(Expression<?> e) {
    MaxIfThenElseDepthVisitor maxIte = new MaxIfThenElseDepthVisitor();
    return maxIte.apply(e);
  }

  public static boolean quantifierCheck(Expression<?> expr) {
    if (expr instanceof QuantifierExpression) {
      return true;
    }

    if (expr instanceof LetExpression) {
      Expression flattened = ((LetExpression) expr).flattenLetExpression();
      Expression<?>[] exprChildren = flattened.getChildren();
      for (Expression i : exprChildren) {
        if (quantifierCheck(i)) {
          return true;
        }
      }
    } else {
      Expression<?>[] exprChildren = expr.getChildren();
      for (Expression i : exprChildren) {
        if (quantifierCheck(i)) {
          return true;
        }
      }
    }
    return false;
  }

  public static boolean checkForForall(Expression<?> expr) {
    if (expr instanceof QuantifierExpression) {
      if (((QuantifierExpression) expr).getQuantifier().equals(Quantifier.FORALL)) {
        return true;
      }
    }

    if (expr instanceof LetExpression) {
      Expression flattened = ((LetExpression) expr).flattenLetExpression();
      Expression<?>[] exprChildren = flattened.getChildren();
      for (Expression i : exprChildren) {
        if (checkForForall(i)) {
          return true;
        }
      }
    } else {
      Expression<?>[] exprChildren = expr.getChildren();
      for (Expression i : exprChildren) {
        if (checkForForall(i)) {
          return true;
        }
      }
    }
    return false;
  }

  public static boolean checkForExists(Expression<?> expr) {
    if (expr instanceof QuantifierExpression) {
      if (((QuantifierExpression) expr).getQuantifier().equals(Quantifier.EXISTS)) {
        return true;
      }
    }
    if (expr instanceof LetExpression) {
      Expression flattened = ((LetExpression) expr).flattenLetExpression();
      Expression<?>[] exprChildren = flattened.getChildren();
      for (Expression i : exprChildren) {
        if (checkForExists(i)) {
          return true;
        }
      }
    } else {
      Expression<?>[] exprChildren = expr.getChildren();
      for (Expression i : exprChildren) {
        if (checkForExists(i)) {
          return true;
        }
      }
    }
    return false;
  }

  public static boolean mixedQuantifierCheck(Expression<?> expr) {
    return (checkForExists(expr) && checkForForall(expr));
  }

  public static int countQuantifiers(Expression<?> expr) {
    QuantifierCounterVisitor quantifierCounter = new QuantifierCounterVisitor();
    return quantifierCounter.apply(expr);
  }

  public static int countItes(Expression<?> expr) {
    IfThenElseCounterVisitor iteCounter = new IfThenElseCounterVisitor();
    return iteCounter.apply(expr);
  }

  public static int countImplys(Expression<?> expr) {
    ImplicationCounterVisitor implyCounter = new ImplicationCounterVisitor();
    return implyCounter.apply(expr);
  }

  public static int countEquivalences(Expression<?> expr) {
    EquivalenceCounterVisitor equivCounter = new EquivalenceCounterVisitor();
    return equivCounter.apply(expr);
  }

  public static int countConjunctions(Expression<?> expr) {
    ConjunctionCounterVisitor conCounter = new ConjunctionCounterVisitor();
    return conCounter.apply(expr);
  }

  public static int countDisjunctions(Expression<?> expr) {
    DisjunctionCounterVisitor disCounter = new DisjunctionCounterVisitor();
    return disCounter.apply(expr);
  }

  public static int countNegations(Expression<?> expr) {
    NegationCounterVisitor negCounter = new NegationCounterVisitor();
    return negCounter.apply(expr);
  }

  public static int countXORs(Expression<?> expr) {
    XORCounterVisitor xorCounter = new XORCounterVisitor();
    return xorCounter.apply(expr);
  }

  public static boolean equivalenceCheck(Expression<?> expr) {
    boolean check = false;
    if (expr instanceof PropositionalCompound) {
      LogicalOperator operator = ((PropositionalCompound) expr).getOperator();
      if (operator.equals(LogicalOperator.EQUIV)) {
        return true;
      }
    }
    if (expr instanceof LetExpression) {
      Expression flattened = ((LetExpression) expr).flattenLetExpression();
      Expression<?>[] exprChildren = flattened.getChildren();
      for (Expression i : exprChildren) {
        if (equivalenceCheck(i)) {
          return true;
        }
      }
    } else {
      Expression<?>[] exprChildren = expr.getChildren();
      for (Expression i : exprChildren) {
        if (equivalenceCheck(i)) {
          return true;
        }
      }
    }
    return false;
  }

  public static boolean ifThenElseCheck(Expression<?> expr) {
    boolean check = false;
    if (expr instanceof IfThenElse) {
      check = true;
      return check;
    }
    if (expr instanceof LetExpression) {
      Expression flattened = ((LetExpression) expr).flattenLetExpression();
      Expression<?>[] exprChildren = flattened.getChildren();
      for (Expression i : exprChildren) {
        if (ifThenElseCheck(i)) {
          check = true;
          return check;
        }
      }
    } else {
      Expression<?>[] exprChildren = expr.getChildren();
      for (Expression i : exprChildren) {
        if (ifThenElseCheck(i)) {
          check = true;
          return check;
        }
      }
    }
    return check;
  }

  // stepcounter methods
  public static int countPushesIntoLogic(Expression e) {
    // make sure, that the same transformations as in reality are performed
    Expression simplified = simplifyProblem(e);
    Expression noEquivalence = eliminateEquivalence(simplified);
    Expression noImplication = eliminateImplication(noEquivalence);
    Expression noXOR = eliminateXOR(noImplication);
    Expression noIte = eliminateIfThenElse(noXOR);
    NegatingVisitor n = new NegatingVisitor();
    n.apply(noIte, false);
    int countNumBoolNegations = n.getCountLogicalNegations();
    return countNumBoolNegations;
  }

  public static int countAllNegationPushes(Expression e) {
    // make sure, that the same transformations as in reality are performed
    Expression simplified = simplifyProblem(e);
    Expression noEquivalence = eliminateEquivalence(simplified);
    Expression noImplication = eliminateImplication(noEquivalence);
    Expression noXOR = eliminateXOR(noImplication);
    Expression noIte = eliminateIfThenElse(noXOR);
    NegatingVisitor n = new NegatingVisitor();
    n.apply(noIte, false);
    int countAllNegationPushs = n.getcountAllNegationPushs();
    return countAllNegationPushs;
  }

  public static int countMiniScopingSteps(Expression e) {
    // make sure, that the same transformations as in reality are performed
    Expression nnf = createNNF(e);
    int countMiniScopingSteps = 0;
    if (quantifierCheck(nnf)) {
      Expression renamed = renameAllBoundVars(nnf);
      // miniscoping is only senseful if there is at least an EXISTS after creation of nnf
      Expression beforeSkolemization;
      if (checkForExists(renamed)) {
        beforeSkolemization = miniScope(renamed);
        MiniScopingVisitor m = new MiniScopingVisitor();
        countMiniScopingSteps = m.countMiniScopeSteps(beforeSkolemization);
      }
    }
    return countMiniScopingSteps;
  }

  public static int countMiniScopingOperationTransformations(Expression e) {
    // make sure, that the same transformations as in reality are performed
    Expression nnf = createNNF(e);
    int operatorTransformations = 0;
    if (quantifierCheck(nnf)) {
      Expression renamed = renameAllBoundVars(nnf);
      // miniscoping is only senseful if there is at least an EXISTS after creation of nnf
      Expression beforeSkolemization;
      if (checkForExists(renamed)) {
        beforeSkolemization = miniScope(renamed);
        MiniScopingVisitor m = new MiniScopingVisitor();
        operatorTransformations = m.countMiniScopeOperatorTransformations(beforeSkolemization);
      }
    }
    return operatorTransformations;
  }

  public static int countCNFSteps(Expression e) {
    // make sure, that the same transformations as in reality are performed
    Expression nnf = createNNF(e);
    ConjunctionCreatorVisitor c = new ConjunctionCreatorVisitor();
    int countCNFSteps = c.countCNFSteps(nnf);
    return countCNFSteps;
  }

  public static int countCNFStepsInMatrix(Expression e) {
    // make sure, that the same transformations as in reality are performed
    Expression nnf = createNNF(e);
    Expression renamed = renameAllBoundVars(nnf);
    // miniscoping is only senseful if there is at least an EXISTS after creation of nnf
    Expression beforeSkolemization;
    if (existsInForall(renamed)) {
      beforeSkolemization = miniScope(renamed);
    } else {
      beforeSkolemization = renamed;
    }
    Expression skolemized = skolemize(beforeSkolemization);
    Expression prenex = prenexing(skolemized);
    if (prenex instanceof QuantifierExpression) {
      Expression body = ((QuantifierExpression) prenex).getBody();
      ConjunctionCreatorVisitor c = new ConjunctionCreatorVisitor();
      int countCNFSteps = c.countCNFSteps(body);
      return countCNFSteps;
    } else {
      ConjunctionCreatorVisitor c = new ConjunctionCreatorVisitor();
      int countCNFSteps = c.countCNFSteps(prenex);
      return countCNFSteps;
    }
  }

  public static int countDNFStepsInMatrix(Expression e) {
    // make sure, that the same transformations as in reality are performed
    Expression nnf = createNNF(e);
    Expression renamed = renameAllBoundVars(nnf);
    // miniscoping is only senseful if there is at least an EXISTS after creation of nnf
    Expression beforeSkolemization;
    if (existsInForall(renamed)) {
      beforeSkolemization = miniScope(renamed);
    } else {
      beforeSkolemization = renamed;
    }
    Expression skolemized = skolemize(beforeSkolemization);
    Expression prenex = prenexing(skolemized);
    if (prenex instanceof QuantifierExpression) {
      Expression body = ((QuantifierExpression) prenex).getBody();
      DisjunctionCreatorVisitor d = new DisjunctionCreatorVisitor();
      int countDNFSteps = d.countDNFSteps(body);
      return countDNFSteps;
    } else {
      DisjunctionCreatorVisitor d = new DisjunctionCreatorVisitor();
      int countDNFSteps = d.countDNFSteps(prenex);
      return countDNFSteps;
    }
  }

  public static int countDNFSteps(Expression e) {
    Expression nnf = createNNF(e);
    DisjunctionCreatorVisitor d = new DisjunctionCreatorVisitor();
    int countDNFSteps = d.countDNFSteps(nnf);
    return countDNFSteps;
  }

  // method for checking if miniscoping is senseful
  public static boolean existsInForall(Expression e) {
    if (e instanceof QuantifierExpression) {
      if (((QuantifierExpression) e).getQuantifier().equals(Quantifier.FORALL)) {
        if (checkForExists(((QuantifierExpression) e).getBody())) {
          return true;
        }
      }
    } else if (e instanceof LetExpression) {
      Expression flattened = ((LetExpression) e).flattenLetExpression();
      Expression<?>[] exprChildren = flattened.getChildren();
      for (Expression i : exprChildren) {
        if (existsInForall(i)) {
          return true;
        }
      }
    } else {
      Expression[] children = e.getChildren();
      for (Expression c : children) {
        if (existsInForall(c)) {
          return true;
        }
      }
    }
    return false;
  }
}
