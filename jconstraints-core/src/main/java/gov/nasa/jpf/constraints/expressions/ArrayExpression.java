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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.ArrayType;
import gov.nasa.jpf.constraints.types.Type;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;
import java.util.Objects;

/**
 * Terms of the theory of arrays: {@code (select a i)}, {@code (store a i v)}, and the constant array {@code ((as
 * const (Array I E)) v)}.
 */
public class ArrayExpression<E> extends AbstractExpression<E> {

  public enum Operator {
    SELECT("select"),
    STORE("store"),
    CONST("const");

    private final String smt;

    Operator(String smt) {
      this.smt = smt;
    }

    @Override
    public String toString() {
      return smt;
    }
  }

  private final Operator operator;
  private final Type<E> type;
  private final Expression<?>[] children;

  private ArrayExpression(Operator operator, Type<E> type, Expression<?>... children) {
    this.operator = operator;
    this.type = type;
    this.children = children;
  }

  /** {@code (select array index)} */
  @SuppressWarnings("unchecked")
  public static <E> ArrayExpression<E> select(Expression<?> array, Expression<?> index) {
    ArrayType t = arrayType(array);
    return new ArrayExpression<>(Operator.SELECT, (Type<E>) t.getElementType(), array, index);
  }

  /** {@code (store array index value)} */
  public static ArrayExpression<Object> store(Expression<?> array, Expression<?> index, Expression<?> value) {
    return new ArrayExpression<>(Operator.STORE, arrayType(array), array, index, value);
  }

  /** the array of the given type with all elements equal to {@code value} */
  public static ArrayExpression<Object> constant(ArrayType type, Expression<?> value) {
    return new ArrayExpression<>(Operator.CONST, type, value);
  }

  private static ArrayType arrayType(Expression<?> array) {
    if (!(array.getType() instanceof ArrayType)) {
      throw new IllegalArgumentException("not an array: " + array);
    }
    return (ArrayType) array.getType();
  }

  public Operator getOperator() {
    return operator;
  }

  public Expression<?> getArray() {
    return operator == Operator.CONST ? null : children[0];
  }

  public Expression<?> getIndex() {
    return operator == Operator.CONST ? null : children[1];
  }

  /** the stored value (STORE) or the value of all elements (CONST) */
  public Expression<?> getValue() {
    return operator == Operator.STORE ? children[2] : operator == Operator.CONST ? children[0] : null;
  }

  @Override
  public E evaluate(Valuation values) {
    throw new UnsupportedOperationException("arrays are not evaluated");
  }

  @Override
  public E evaluateSMT(Valuation values) {
    throw new UnsupportedOperationException("arrays are not evaluated");
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    for (Expression<?> c : children) {
      c.collectFreeVariables(variables);
    }
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  @Override
  public Type<E> getType() {
    return type;
  }

  @Override
  public Expression<?>[] getChildren() {
    return children.clone();
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    if (Arrays.equals(children, newChildren)) {
      return this;
    }
    return new ArrayExpression<>(operator, type, newChildren.clone());
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    if (operator == Operator.CONST) {
      a.append("((as const ").append(type.getName()).append(") ");
    } else {
      a.append("(").append(operator.toString()).append(" ");
    }
    for (int i = 0; i < children.length; i++) {
      if (i > 0) {
        a.append(" ");
      }
      children[i].print(a, flags);
    }
    a.append(")");
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    print(a, flags);
  }

  @Override
  public boolean equals(Object o) {
    if (!(o instanceof ArrayExpression)) {
      return false;
    }
    ArrayExpression<?> e = (ArrayExpression<?>) o;
    return operator == e.operator && Objects.equals(type, e.type) && Arrays.equals(children, e.children);
  }

  @Override
  public int hashCode() {
    return Objects.hash(operator, type.getName(), Arrays.hashCode(children));
  }
}
