/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2023 The jConstraints Authors
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
import gov.nasa.jpf.constraints.types.BVIntegerType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import java.io.IOException;
import java.util.Collection;

public class BitVectorFunction<F, T> extends AbstractExpression<T> {

  public enum BVFCT {
    SIGN_EXTEND,
    ZERO_EXTEND,
    EXTRACT
  };

  private final BVFCT function;

  private final int[] params;

  private final Type<T> type;

  private final Expression<F> argument;

  private BitVectorFunction(BVFCT function, Type<T> type, Expression<F> argument, int... params) {
    this.function = function;
    this.type = type;
    this.argument = argument;
    this.params = params;
  }

  @Override
  public T evaluate(Valuation values) {
    throw new UnsupportedOperationException("not yet implemented");
  }

  @Override
  public T evaluateSMT(Valuation values) {
    throw new UnsupportedOperationException("not yet implemented");
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    argument.collectFreeVariables(variables);
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  @Override
  public Type<T> getType() {
    return type;
  }

  @Override
  public Expression<?>[] getChildren() {
    return new Expression[] {argument};
  }

  public BVFCT getFunction() {
    return function;
  }

  public int[] getParams() {
    return params;
  }

  public Expression<F> getArgument() {
    return argument;
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    throw new UnsupportedOperationException("not yet implemented");
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append("((_ ");
    switch (function) {
      case SIGN_EXTEND:
        a.append("sign_extend");
        break;
      case ZERO_EXTEND:
        a.append("zero_extend");
        break;
      case EXTRACT:
        a.append("extract");
        break;
    }
    for (int p : params) {
      a.append(" " + p);
    }
    a.append(") ");
    argument.print(a, flags);
    a.append(")");
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    throw new UnsupportedOperationException("not yet implemented");
  }

  public static <F, T> BitVectorFunction<F, T> signExtend(int byBits, Expression<F> argument) {
    BVIntegerType<F> argType = (BVIntegerType) argument.getType();
    int toBits = argType.getNumBits() + byBits;
    Type<?> type = typeForBits(toBits);
    return new BitVectorFunction(BVFCT.SIGN_EXTEND, type, argument, byBits);
  }

  public static <F, T> BitVectorFunction<F, T> zeroExtend(int byBits, Expression<F> argument) {
    BVIntegerType<F> argType = (BVIntegerType) argument.getType();
    int toBits = argType.getNumBits() + byBits;
    Type<?> type = typeForBits(toBits);
    return new BitVectorFunction(BVFCT.ZERO_EXTEND, type, argument, byBits);
  }

  public static <F, T> BitVectorFunction<F, T> extract(
      int highBit, int lowBit, Expression<F> argument) {
    Type<?> type = typeForBits(highBit - lowBit + 1);
    return new BitVectorFunction(BVFCT.EXTRACT, type, argument, highBit, lowBit);
  }

  public static Type<?> typeForBits(int bits) {
    switch (bits) {
      case 8:
        return BuiltinTypes.SINT8;
      case 16:
        return BuiltinTypes.SINT16;
      case 32:
        return BuiltinTypes.SINT32;
      case 64:
        return BuiltinTypes.SINT64;
      default:
        throw new IllegalArgumentException("Unsupported bitSize: " + bits);
    }
  }
}
