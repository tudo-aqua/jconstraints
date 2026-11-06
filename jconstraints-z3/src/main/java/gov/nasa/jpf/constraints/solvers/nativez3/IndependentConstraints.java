/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2026 The jConstraints Authors
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

package gov.nasa.jpf.constraints.solvers.nativez3;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.FloatingPointType;
import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

/**
 * Constraint independence (as in KLEE): partitions a conjunction into groups of conjuncts that
 * share no symbol (variable or uninterpreted function). The conjunction is satisfiable iff every
 * group is, and the union of models of the groups is a model of the conjunction.
 *
 * <p>Solving the groups separately keeps Z3 from choosing its strategy for the logic of the whole
 * conjunction: e.g., an unrelated integer or string constraint makes Z3 solve floating-point
 * constraints with the general SMT core instead of bit-blasting them, which can take orders of
 * magnitude longer.
 */
final class IndependentConstraints {

  private IndependentConstraints() {}

  /** the conjuncts of {@code e}: nested conjunctions are flattened, {@code true} is dropped */
  static void flatten(Expression<Boolean> e, List<Expression<Boolean>> out) {
    Deque<Expression<Boolean>> todo = new ArrayDeque<>();
    todo.push(e);
    while (!todo.isEmpty()) {
      Expression<Boolean> cur = todo.pop();
      if (cur instanceof PropositionalCompound
          && ((PropositionalCompound) cur).getOperator() == LogicalOperator.AND) {
        todo.push(((PropositionalCompound) cur).getRight());
        todo.push(((PropositionalCompound) cur).getLeft());
      } else if (!ExpressionUtil.TRUE.equals(cur)) {
        out.add(cur);
      }
    }
  }

  /** the symbols of {@code e}: names of variables and (prefixed) names of functions */
  static Set<String> symbols(Expression<?> e) {
    Set<String> symbols = new LinkedHashSet<>();
    Deque<Expression<?>> todo = new ArrayDeque<>();
    // shared subterms (e.g. the ite terms of heap models) are visited once
    Set<Expression<?>> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    todo.push(e);
    while (!todo.isEmpty()) {
      Expression<?> cur = todo.pop();
      if (!seen.add(cur)) {
        continue;
      }
      if (cur instanceof Variable) {
        symbols.add("v:" + ((Variable<?>) cur).getName());
      } else if (cur instanceof FunctionExpression) {
        symbols.add("f:" + ((FunctionExpression<?>) cur).getFunction().getName());
      }
      if (cur instanceof LetExpression) {
        // no children (getChildren throws): the bound values and the body (bound variables count as
        // symbols in the
        // body, which only merges groups)
        LetExpression let = (LetExpression) cur;
        for (Object v : let.getParameterValues().values()) {
          todo.push((Expression<?>) v);
        }
        todo.push(let.getMainValue());
        continue;
      }
      Expression<?>[] children = cur.getChildren();
      if (children != null) {
        for (Expression<?> c : children) {
          if (c != null) {
            todo.push(c);
          }
        }
      }
    }
    return symbols;
  }

  /** whether a subterm of {@code group} is a string or a regular expression */
  static boolean usesStrings(List<Expression<Boolean>> group) {
    return hasSubtermOfType(
        group, t -> BuiltinTypes.STRING.equals(t) || BuiltinTypes.REGEX.equals(t));
  }

  /** whether a subterm of {@code group} is a floating-point number */
  static boolean usesFloatingPoint(List<Expression<Boolean>> group) {
    return hasSubtermOfType(group, t -> t instanceof FloatingPointType);
  }

  private static boolean hasSubtermOfType(
      List<Expression<Boolean>> group, Predicate<Type<?>> typeTest) {
    Deque<Expression<?>> todo = new ArrayDeque<>(group);
    Set<Expression<?>> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    while (!todo.isEmpty()) {
      Expression<?> cur = todo.pop();
      if (!seen.add(cur)) {
        continue;
      }
      try {
        if (typeTest.test(cur.getType())) {
          return true;
        }
      } catch (RuntimeException e) {
        // no type: look at the children
      }
      if (cur instanceof LetExpression) {
        LetExpression let = (LetExpression) cur;
        for (Object v : let.getParameterValues().values()) {
          todo.push((Expression<?>) v);
        }
        todo.push(let.getMainValue());
        continue;
      }
      Expression<?>[] children = cur.getChildren();
      if (children != null) {
        for (Expression<?> c : children) {
          if (c != null) {
            todo.push(c);
          }
        }
      }
    }
    return false;
  }

  /**
   * Partitions {@code conjuncts} into groups without shared symbols (union-find over the symbols),
   * in the order of their first conjunct. Conjuncts without symbols form a group of their own.
   */
  static List<List<Expression<Boolean>>> partition(List<Expression<Boolean>> conjuncts) {
    int n = conjuncts.size();
    int[] parent = new int[n];
    for (int i = 0; i < n; i++) {
      parent[i] = i;
    }
    Map<String, Integer> owner = new HashMap<>();
    for (int i = 0; i < n; i++) {
      for (String s : symbols(conjuncts.get(i))) {
        Integer j = owner.putIfAbsent(s, i);
        if (j != null) {
          union(parent, i, j);
        }
      }
    }
    Map<Integer, List<Expression<Boolean>>> groups = new LinkedHashMap<>();
    for (int i = 0; i < n; i++) {
      groups.computeIfAbsent(find(parent, i), k -> new ArrayList<>()).add(conjuncts.get(i));
    }
    return new ArrayList<>(groups.values());
  }

  private static int find(int[] parent, int i) {
    while (parent[i] != i) {
      parent[i] = parent[parent[i]];
      i = parent[i];
    }
    return i;
  }

  private static void union(int[] parent, int a, int b) {
    int ra = find(parent, a);
    int rb = find(parent, b);
    if (ra != rb) {
      parent[Math.max(ra, rb)] = Math.min(ra, rb);
    }
  }
}
