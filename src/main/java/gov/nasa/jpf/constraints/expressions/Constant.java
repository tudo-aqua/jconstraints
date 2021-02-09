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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.java.ObjectConstraints;
import gov.nasa.jpf.constraints.types.BuiltinTypes.BigDecimalType;
import gov.nasa.jpf.constraints.types.Type;
import java.io.IOException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collection;

/** constant value of type E */
public class Constant<E> extends AbstractExpression<E> {

  private final Type<E> type;
  private final E value;

  public Constant(Type<E> type, E value) {
    this.type = type;
    assert this.type.getDefaultValue().getClass().isInstance(value);
    this.value = value;
  }

  @Deprecated
  public Constant(Class<E> clazz, E value) {
    this(ObjectConstraints.getPrimitiveType(clazz), value);
  }

  public static <E> Constant<E> create(Type<E> type, E value) {
    return new Constant<E>(type, value);
  }

  public static <E> Constant<E> createParsed(Type<E> type, String txt)
      throws ImpreciseRepresentationException {
    return new Constant<E>(type, type.parse(txt));
  }

  public static <E> Constant<E> createCasted(Type<E> type, Constant c) {
    return createCasted(type, c.value);
  }

  public static <E> Constant<E> createCasted(Type<E> type, Object value) {
    if (type instanceof BigDecimalType && value instanceof BigInteger) {
      BigDecimal val = BigDecimal.valueOf(((BigInteger) value).longValue());
      return (Constant<E>) new Constant<BigDecimal>((Type<BigDecimal>) type, val);
    }
    return new Constant<E>(type, type.cast(value));
  }

  @Override
  public E evaluate(Valuation values) {
    return this.value;
  }

  @Override
  public E evaluateSMT(Valuation values) {
    return evaluate(values);
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    // do nothing
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    final Constant<?> other = (Constant<?>) obj;
    if (this.type != other.type && (this.type == null || !this.type.equals(other.type))) {
      return false;
    }
    if ((this.value == null) ? (other.value != null) : !this.value.equals(other.value)) {
      return false;
    }
    return true;
  }

  @Override
  public int hashCode() {
    int hash = 7;
    hash = 47 * hash + (this.type != null ? this.type.hashCode() : 0);
    hash = 47 * hash + (this.value != null ? this.value.hashCode() : 0);
    return hash;
  }

  @Override
  public Type<E> getType() {
    return this.type;
  }

  public E getValue() {
    return this.value;
  }

  @Override
  public Expression<?>[] getChildren() {
    return NO_CHILDREN;
  }

  @Override
  public Expression<E> duplicate(Expression<?>[] newChildren) {
    assert newChildren.length == 0;
    return this;
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append(String.valueOf(value));
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    if (value == null) {
      a.append("null");
    } else {
      a.append(String.valueOf(value));
    }
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }
}
