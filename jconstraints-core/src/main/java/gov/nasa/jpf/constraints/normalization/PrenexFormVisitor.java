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
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

import java.util.*;

//needed for creation of CNFs or DNFs in presence of quantifiers
public class PrenexFormVisitor extends
    DuplicatingVisitor<Void> {

  private static final PrenexFormVisitor INSTANCE = new PrenexFormVisitor();

  public static PrenexFormVisitor getInstance(){
    return INSTANCE;
  }

  Set<Variable<?>> boundVarsForall = new HashSet<>();

  @Override
  public Expression<?> visit(QuantifierExpression q, Void data) {

    if (q.getQuantifier().equals(Quantifier.EXISTS)) {
      throw new UnsupportedOperationException("EXISTS detected, skolemize first!");
    }
    Expression<Boolean> body = q.getBody();
    return visit(body, data);
  }

  @Override
  //Not needed if LetExpressionRemover is used beforehand
  public Expression<?> visit(LetExpression expr, Void data) {
    Expression flattened = expr.flattenLetExpression();
    Expression result = visit(flattened, data);
    return result;
  }

  public <T> Expression<T> apply(Expression<T> expr, Void data) {
    boundVarsForall = ExpressionUtil.boundVariables(expr);
    List<Variable<?>> bound = new ArrayList<>();
    bound.addAll(boundVarsForall);
    Expression matrix = visit(expr, data).requireAs(expr.getType());
    if(!bound.isEmpty()){
      Expression result = QuantifierExpression.create(Quantifier.FORALL, bound, matrix);
      return result;
    } else {
      return expr;
    }
  }
}