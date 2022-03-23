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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import java.io.IOException;
import java.util.Collection;

public class FloatingPointBooleanExpression extends AbstractExpression<Boolean> {

  private final FPComparator operator;

  private final Expression[] children;

  public FloatingPointBooleanExpression(FPComparator operator, Expression<Boolean>... children) {
    this.operator = operator;
    this.children = children;
  }

  public FPComparator getOperator() {
    return operator;
  }

  @Override
  public Boolean evaluate(Valuation values) {
    throw new UnsupportedOperationException("not yet implemented");
  }

  @Override
  public Boolean evaluateSMT(Valuation values) {
    throw new UnsupportedOperationException("not yet implemented");
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    for (Expression e : children) {
      e.collectFreeVariables(variables);
    }
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  @Override
  public Type<Boolean> getType() {
    return BuiltinTypes.BOOL;
  }

  @Override
  public Expression<Boolean>[] getChildren() {
    return children;
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    throw new UnsupportedOperationException("not yet implemented");
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append("(");
    a.append(this.operator.toString());
    for (Expression e : this.children) {
      a.append(" ");
      e.print(a, flags);
    }
    a.append(")");
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    throw new UnsupportedOperationException("not yet implemented");
  }
}
