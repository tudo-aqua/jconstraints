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

/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * <p>This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * <p>Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377 the original license
 * is: Copyright (C) 2015, United States Government, as represented by the Administrator of the
 * National Aeronautics and Space Administration. All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment platform is licensed
 * under the Apache License, Version 2.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues under Apache
 * 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.normalization.analysis;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;

public class QuantifierCheckVisitor extends AbstractExpressionVisitor {

  private static final QuantifierCheckVisitor INSTANCE = new QuantifierCheckVisitor();

  public static QuantifierCheckVisitor getInstance(){
    return INSTANCE;
  }

  @Override
  public Object visit(QuantifierExpression q, Object data) {
    return true;
  }

  @Override
  public Expression<?> visit(LetExpression expr, Object data) {
    Expression flattened = expr.flattenLetExpression();
    Expression result = (Expression) visit(flattened, data);
    return result;
  }

  @Override
  protected Object defaultVisit(Expression expression, Object data) {
    Expression<?>[] exprChildren = expression.getChildren();
    for(Expression i : exprChildren){
      return visit(i, null);
    }
    return false;
  }
}
