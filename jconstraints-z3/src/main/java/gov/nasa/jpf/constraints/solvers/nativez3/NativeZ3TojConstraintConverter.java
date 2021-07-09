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

package gov.nasa.jpf.constraints.solvers.nativez3;

import com.microsoft.z3.*;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.types.ArrayType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

import java.util.ArrayList;
import java.util.logging.Level;
import java.util.logging.Logger;

public class NativeZ3TojConstraintConverter {

  private Logger logger;

  public NativeZ3TojConstraintConverter() {
    logger = Logger.getLogger("z3");
  }

  public Expression parse(Expr z3Expr) throws ImpreciseRepresentationException {
    logger.info("parse:" + z3Expr);
    Expression returnExpression = null;
    ArrayList<Expression<Boolean>> arguments = convertArgs(z3Expr.getArgs());
    try {
      if (z3Expr.isAnd()) {
        returnExpression = ExpressionUtil.and(arguments);
      }
    } catch (IllegalArgumentException e) {
      logger.warning("isAnd failed");
    }
    try {
      if (z3Expr.isOr()) {
        returnExpression = ExpressionUtil.or(arguments);
      }
    } catch (IllegalArgumentException e) {
      logger.warning("isOr failed");
    }
    try {
      if (z3Expr.isXor()) {
        returnExpression = ExpressionUtil.combine(LogicalOperator.XOR, null, arguments);
      }
    } catch (IllegalArgumentException e) {
      logger.warning("isXor failed");
    }

    if (z3Expr instanceof BoolExpr) {
      if (z3Expr.isTrue()) {
        returnExpression = Constant.create(BuiltinTypes.BOOL, true);
      } else if (z3Expr.isFalse()) {
        returnExpression = Constant.create(BuiltinTypes.BOOL, false);
      } else {
        // This is actually happening in z3Expr... Fix me
        returnExpression = new Variable(BuiltinTypes.BOOL, z3Expr.toString());
      }
    }
    if (z3Expr instanceof IntNum) {
      String value = ((IntNum) z3Expr).toString();
      returnExpression = Constant.createParsed(BuiltinTypes.INTEGER, value);
    }
    if (z3Expr instanceof IntExpr) {
      String name = ((IntExpr) z3Expr).toString();
      returnExpression = new Variable(BuiltinTypes.INTEGER, name);
    }
    if (z3Expr instanceof BitVecExpr) {
      try {
        returnExpression = parseBitVector(z3Expr, arguments);
      } catch (Exception ex) {
        logger.log(Level.SEVERE, null, ex);
      }
    }
    if (z3Expr instanceof ArrayExpr) {
      ArrayExpr arrayExpr = (ArrayExpr) z3Expr;
      //argument size == 3 - store
      //argument size == 2 - select
      //argument size == 0 - new array
      String name = arrayExpr.toString();
      ArrayType arrayType = parseArrayType((ArraySort) arrayExpr.getSort());
      returnExpression = new Variable(arrayType, name);
    }
    if (arguments.size() == 1) {
      if (z3Expr.isUMinus()) {
        returnExpression = UnaryMinus.create(arguments.get(0));
      }
      if (z3Expr.isNot()) {
        returnExpression = new Negation(arguments.get(0));
      }
    }
    if (arguments.size() == 2) {
      if (z3Expr.isAdd()) {
        returnExpression =
            NumericCompound.create(arguments.get(0), NumericOperator.PLUS, arguments.get(1));
      }
      if (z3Expr.isMul()) {
        returnExpression =
            NumericCompound.create(arguments.get(0), NumericOperator.MUL, arguments.get(1));
      }
      if (z3Expr.isDiv()) {
        returnExpression =
            NumericCompound.create(arguments.get(0), NumericOperator.DIV, arguments.get(1));
      }
      if (z3Expr.isRemainder()) {
        returnExpression =
            NumericCompound.create(arguments.get(0), NumericOperator.REM, arguments.get(1));
      }
      if (z3Expr.isSub()) {
        returnExpression =
            NumericCompound.create(arguments.get(0), NumericOperator.MINUS, arguments.get(1));
      }
      if (z3Expr.isGT()) {
        returnExpression =
            NumericBooleanExpression.create(
                arguments.get(0), NumericComparator.GT, arguments.get(1));
      }
      if (z3Expr.isGE()) {
        returnExpression =
            NumericBooleanExpression.create(
                arguments.get(0), NumericComparator.GE, arguments.get(1));
      }
      if (z3Expr.isLT()) {
        returnExpression =
            NumericBooleanExpression.create(
                arguments.get(0), NumericComparator.LT, arguments.get(1));
      }
      if (z3Expr.isLE()) {
        returnExpression =
            NumericBooleanExpression.create(
                arguments.get(0), NumericComparator.LE, arguments.get(1));
      }
      if (z3Expr.isEq()) {
        returnExpression =
            NumericBooleanExpression.create(
                arguments.get(0), NumericComparator.EQ, arguments.get(1));
      }
      if (z3Expr.isModulus()) {
        throw new UnsupportedOperationException("jConstraint does not support Modulus yet.");
      }
    }
    if (returnExpression == null) {
      String msg = "Cannot convert the z3Expression to jConstraint";
      logger.severe(msg);
      throw new UnsupportedOperationException(msg);
    }
    return returnExpression;
  }

  private ArrayList<Expression<Boolean>> convertArgs(Expr[] args)
      throws ImpreciseRepresentationException {
    ArrayList<Expression<Boolean>> converted = new ArrayList<>();
    for (Expr expr : args) {
      converted.add(parse(expr));
    }
    return converted;
  }

  private Expression<Boolean> parseBitVector(Expr z3Expr, ArrayList<Expression<Boolean>> arguments)
      throws Exception {
    if (z3Expr.isBVAND()) {
      return new BitvectorExpression<>(arguments.get(0), BitvectorOperator.AND, arguments.get(1));
    }
    if (z3Expr.isBVSLT()) {
      return new NumericBooleanExpression(arguments.get(0), NumericComparator.LT, arguments.get(1));
    }
    if (z3Expr instanceof BitVecExpr) {
      if (z3Expr.isInt()) {
        return new Variable(BuiltinTypes.INTEGER, z3Expr.toString());
      }
      switch (z3Expr.getSort().getSortKind()) {
        case Z3_BOOL_SORT:
          return new Variable(BuiltinTypes.BOOL, z3Expr.toString());
        case Z3_INT_SORT:
          return new Variable(BuiltinTypes.INTEGER, z3Expr.toString());
        case Z3_REAL_SORT:
          return new Variable(BuiltinTypes.DECIMAL, z3Expr.toString());
        case Z3_BV_SORT:
          return new Variable(BuiltinTypes.INTEGER, z3Expr.toString());
        default:
          throw new Exception("Unknown NamedSort");
      }
    }
    return null;
  }


  private ArrayType parseArrayType(ArraySort arraySort) {
    Sort domain = arraySort.getDomain();
    Sort range = arraySort.getRange();
    return new ArrayType(parseType(domain), parseType(range));
  }

  private Type parseType(Sort sort) {
    if (sort instanceof IntSort) return BuiltinTypes.INTEGER;
    if (sort instanceof BoolSort) return BuiltinTypes.BOOL;
    if (sort instanceof RealSort) return BuiltinTypes.REAL;
    if (sort instanceof ArraySort) return parseArrayType((ArraySort) sort);
    throw new UnsupportedOperationException("Sort is not supported for conversion!");
  }
}
