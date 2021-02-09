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

package gov.nasa.jpf.constraints.util;

import com.google.common.base.Function;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.simplifiers.datastructures.ArithmeticVarReplacements;

class TransformVarVisitor
    extends DuplicatingVisitor<Function<? super Variable<?>, ? extends Expression<?>>> {

  private static final TransformVarVisitor INSTANCE = new TransformVarVisitor();

  public static TransformVarVisitor getInstance() {
    return INSTANCE;
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.api.Variable,
   *  java.lang.Object)
   */
  @Override
  public <E> Expression<?> visit(
      Variable<E> v, Function<? super Variable<?>, ? extends Expression<?>> data) {
    return data.apply(v);
  }

  @Override
  public Expression<?> visit(
      LetExpression let, Function<? super Variable<?>, ? extends Expression<?>> data) {
    if (data instanceof ArithmeticVarReplacements) {
      ArithmeticVarReplacements replacements = (ArithmeticVarReplacements) data;
      replacements.putAll(let.getParameterValues());
      return visit(let.getMainValue(), data);
    }
    throw new UnsupportedOperationException("Don't know, what is expected here");
  }

  public <T> Expression<T> apply(
      Expression<T> expr, Function<? super Variable<?>, ? extends Expression<?>> transform) {
    return visit(expr, transform).requireAs(expr.getType());
  }
}
