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
import gov.nasa.jpf.constraints.expressions.*;

public class DisjunctionCounterVisitor extends AbstractExpressionVisitor<Integer, Void> {

  private static final DisjunctionCounterVisitor INSTANCE = new DisjunctionCounterVisitor();

  public static DisjunctionCounterVisitor getInstance(){
    return INSTANCE;
  }

  private final int countDisjunctions(Expression<?>... children) {
    if (children.length == 0) return 0;

    int counter = children[0].accept(this, null);
    for (int i = 1; i < children.length; i++) {
      int d = visit(children[i], null);
      counter+= d;
    }
    return counter;
  }

  @Override
  public Integer visit(PropositionalCompound n, Void data) {
    if (n.getOperator().equals(LogicalOperator.OR)){
      return 1 + countDisjunctions(n.getChildren());
    } else {
      return countDisjunctions(n.getChildren());
    }
  }

  @Override
  public Integer visit(QuantifierExpression q, Void data) {
    return countDisjunctions(q.getBody());
  }

  @Override
  protected <E> Integer defaultVisit(Expression<E> expression, Void data) {
    return countDisjunctions(expression.getChildren());
  }

  @Override
  public Integer visit(LetExpression let, Void data) {
    return countDisjunctions(let.flattenLetExpression());
  }

  public int apply(Expression<?> expr) {
    return visit(expr, null);
  }
}
