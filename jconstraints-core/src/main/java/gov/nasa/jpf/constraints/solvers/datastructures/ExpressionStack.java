/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2022 The jConstraints Authors
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

package gov.nasa.jpf.constraints.solvers.datastructures;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

public class ExpressionStack {

  private final Deque<List<Expression>> stack;
  private List<Expression> current;

  public ExpressionStack() {
    stack = new LinkedList<>();
    current = new LinkedList<>();
  }

  public void push() {
    stack.push(current);
    current = new LinkedList<>();
  }

  public void pop(int n) {
    for (int i = 0; i < n; i++) {
      current = stack.pop();
    }
  }

  public void add(List<Expression<Boolean>> expressions) {
    current.addAll(expressions);
  }

  public List<Expression<Boolean>> getCurrentExpression() {
    List<Expression<Boolean>> currentExpr = new LinkedList<>();
    for (List<Expression> list : stack) {
      for (Expression e : list) {
        currentExpr.add(e);
      }
    }
    for (Expression e : current) {
      currentExpr.add(e);
    }
    return currentExpr;
  }

  public List<Variable<?>> getVarsInStack() {
    return new LinkedList<>(
        ExpressionUtil.freeVariables(ExpressionUtil.and(getCurrentExpression())));
  }
}
