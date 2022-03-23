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
import gov.nasa.jpf.constraints.types.BVIntegerType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.FloatingPointType;
import gov.nasa.jpf.constraints.types.Type;
import java.io.IOException;
import java.util.Collection;

public class FloatingPointFunction<F, T> extends AbstractExpression<T> {

  public enum FPFCT {
    FP_ABS,
    FP_NEG,
    TO_FP_FROM_BITSTRING,
    TO_FP_FROM_FP,
    TO_FP_FROM_REAL,
    TO_FP_FROM_SBV,
    TO_FP_FROM_UBV,
    FP_ADD,
    FP_SUB,
    FP_MUL,
    FP_DIV,
    FP_FMA,
    FP_SQRT,
    FP_REM,
    FP_ROUND_TO_INTEGRAL,
    FP_MIN,
    FP_MAX,
    FP_TO_SBV,
    FP_TO_UBV,
    FP_TO_REAL,
    _FP_RND
  };

  private final FPFCT function;

  private final int[] params;

  private final Type<T> type;

  private final Expression<F>[] arguments;

  private final FPRoundingMode rmode;

  private FloatingPointFunction(
      FPFCT function,
      Type<T> type,
      FPRoundingMode rmode,
      int[] params,
      Expression<F>... arguments) {
    this.function = function;
    this.type = type;
    this.arguments = arguments;
    this.params = params;
    this.rmode = rmode;
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
    for (Expression e : arguments) {
      e.collectFreeVariables(variables);
    }
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
  public Expression<F>[] getChildren() {
    return arguments;
  }

  public FPFCT getFunction() {
    return function;
  }

  public FPRoundingMode getRmode() {
    return rmode;
  }

  public int[] getParams() {
    return params;
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    throw new UnsupportedOperationException("not yet implemented");
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append("(");
    switch (function) {
      case FP_ADD:
        a.append("fp.add");
        break;
      case FP_SUB:
        a.append("fp.sub");
        break;
      case FP_MUL:
        a.append("fp.mul");
        break;
      case FP_DIV:
        a.append("fp.div");
        break;
      case FP_REM:
        a.append("fp.rem");
        break;
      case TO_FP_FROM_BITSTRING:
        a.append("(_ to_fp ").append("" + params[0]).append(" ").append("" + params[1]).append(")");
        break;
      case TO_FP_FROM_FP:
      case TO_FP_FROM_REAL:
      case TO_FP_FROM_SBV:
      case TO_FP_FROM_UBV:
        a.append("(_ to_fp ")
            // .append(" (")
            // .append(rmode.toString())
            // .append(" RoundingMode)")
            .append(" " + params[0])
            .append(" ")
            .append("" + params[1])
            .append(")");
        break;
      case FP_TO_SBV:
        a.append("(_ to_sbv ")
            // .append(" (")
            // .append(rmode.toString())
            // .append(" RoundingMode)")
            .append(" " + params[0])
            // .append(" ")
            // .append("" + params[0])
            .append(")");
        break;
      case FP_TO_UBV:
        a.append("(_ to_ubv ")
            // .append(" (")
            // .append(rmode.toString())
            // .append(" RoundingMode)")
            .append(" " + params[0])
            .append(" ")
            .append("" + params[0])
            .append(")");
        break;
      case FP_TO_REAL:
        a.append("(_ to_real ")
            .append("" + params[0])
            .append(" ")
            .append("" + params[1])
            .append(")");
        break;
    }
    if (rmode != null) a.append(" (").append(rmode.toString()).append(" RoundingMode)");
    for (Expression arg : arguments) {
      a.append(" ");
      arg.print(a, flags);
    }
    a.append(")");
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    throw new UnsupportedOperationException("not yet implemented");
  }

  public static <T> FloatingPointFunction<T, T> fpadd(
      FPRoundingMode rmode, Expression<T> left, Expression<T> right) {
    return new FloatingPointFunction(FPFCT.FP_ADD, left.getType(), rmode, null, left, right);
  }

  public static <T> FloatingPointFunction<T, T> fpsub(
      FPRoundingMode rmode, Expression<T> left, Expression<T> right) {
    return new FloatingPointFunction(FPFCT.FP_SUB, left.getType(), rmode, null, left, right);
  }

  public static <T> FloatingPointFunction<T, T> fpmul(
      FPRoundingMode rmode, Expression<T> left, Expression<T> right) {
    return new FloatingPointFunction(FPFCT.FP_MUL, left.getType(), rmode, null, left, right);
  }

  public static <T> FloatingPointFunction<T, T> fpdiv(
      FPRoundingMode rmode, Expression<T> left, Expression<T> right) {
    return new FloatingPointFunction(FPFCT.FP_DIV, left.getType(), rmode, null, left, right);
  }

  public static <T> FloatingPointFunction<T, T> fpsqrt(FPRoundingMode rmode, Expression<T> inner) {
    return new FloatingPointFunction(FPFCT.FP_SQRT, inner.getType(), rmode, null, inner);
  }

  public static <T> FloatingPointFunction<T, T> fpRoundToIntegral(
      FPRoundingMode rmode, Expression<T> inner) {
    return new FloatingPointFunction(
        FPFCT.FP_ROUND_TO_INTEGRAL, inner.getType(), rmode, null, inner);
  }

  public static <T> FloatingPointFunction<T, T> fpfma(
      FPRoundingMode rmode, Expression<T> left, Expression<T> middle, Expression<T> right) {
    return new FloatingPointFunction(
        FPFCT.FP_FMA, left.getType(), rmode, null, left, middle, right);
  }

  public static <T> FloatingPointFunction<T, T> fprem(Expression<T> left, Expression<T> right) {
    return new FloatingPointFunction(FPFCT.FP_REM, left.getType(), null, null, left, right);
  }

  public static <T> FloatingPointFunction<T, T> fpneg(Expression<T> inner) {
    return new FloatingPointFunction(FPFCT.FP_NEG, inner.getType(), null, null, inner);
  }

  public static <T> FloatingPointFunction<T, T> fpabs(Expression<T> inner) {
    return new FloatingPointFunction(FPFCT.FP_ABS, inner.getType(), null, null, inner);
  }

  public static <T> FloatingPointFunction<T, T> fp_min(Expression<T> left, Expression<T> right) {
    return new FloatingPointFunction(FPFCT.FP_MIN, left.getType(), null, null, left, right);
  }

  public static <T> FloatingPointFunction<T, T> fp_max(Expression<T> left, Expression<T> right) {
    return new FloatingPointFunction(FPFCT.FP_MAX, left.getType(), null, null, left, right);
  }

  public static <F, T> FloatingPointFunction<F, T> tofpFromBitstring(
      Expression<F> inner, int mBits, int eBits) {
    return new FloatingPointFunction(
        FPFCT.TO_FP_FROM_BITSTRING,
        typeForBits(mBits, eBits),
        null,
        new int[] {eBits, mBits},
        inner);
  }

  public static <F, T> FloatingPointFunction<F, T> tofpFromFp(
      FPRoundingMode rmode, Expression<F> inner, int mBits, int eBits) {
    return new FloatingPointFunction(
        FPFCT.TO_FP_FROM_FP, typeForBits(mBits, eBits), rmode, new int[] {eBits, mBits}, inner);
  }

  public static <F, T> FloatingPointFunction<F, T> tofpFromReal(
      FPRoundingMode rmode, Expression<F> inner, int mBits, int eBits) {
    return new FloatingPointFunction(
        FPFCT.TO_FP_FROM_REAL, typeForBits(mBits, eBits), rmode, new int[] {eBits, mBits}, inner);
  }

  public static <F, T> FloatingPointFunction<F, T> tofpFromBV(
      FPRoundingMode rmode, Expression<F> inner, int mBits, int eBits) {
    return new FloatingPointFunction(
        ((BVIntegerType) inner.getType()).isSigned() ? FPFCT.TO_FP_FROM_SBV : FPFCT.TO_FP_FROM_UBV,
        typeForBits(mBits, eBits),
        rmode,
        new int[] {eBits, mBits},
        inner);
  }

  public static <F, T> FloatingPointFunction<F, T> tosbv(
      FPRoundingMode rmode, Expression<F> inner, int bits) {
    Type<?> type = BitVectorFunction.typeForBits(bits);
    return new FloatingPointFunction(FPFCT.FP_TO_SBV, type, rmode, new int[] {bits}, inner);
  }

  public static <F, T> FloatingPointFunction<F, T> toubv(
      FPRoundingMode rmode, Expression<F> inner, int bits) {
    Type<?> type = BitVectorFunction.typeForBits(bits);
    return new FloatingPointFunction(FPFCT.FP_TO_UBV, type, rmode, new int[] {bits}, inner);
  }

  public static <F, T> FloatingPointFunction<F, T> toreal(Expression<F> inner) {
    return new FloatingPointFunction(
        FPFCT.FP_TO_REAL, BuiltinTypes.REAL, null, new int[] {}, inner);
  }

  public static <T> FloatingPointFunction<T, T> _rndMode(FPRoundingMode rnd) {
    return new FloatingPointFunction(FPFCT._FP_RND, null, rnd, null);
  }

  private static FloatingPointType<?> typeForBits(int mBits, int eBits) {
    if (mBits == 53 && eBits == 11) {
      return BuiltinTypes.DOUBLE;
    }
    if (mBits == 24 && eBits == 8) {
      return BuiltinTypes.FLOAT;
    } else {
      throw new IllegalArgumentException("Unsupported fp size: " + mBits + ":" + eBits);
    }
  }
}
