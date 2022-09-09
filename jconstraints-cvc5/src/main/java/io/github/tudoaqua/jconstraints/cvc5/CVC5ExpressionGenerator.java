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

package io.github.tudoaqua.jconstraints.cvc5;

import static io.github.cvc5.Kind.ADD;
import static io.github.cvc5.Kind.AND;
import static io.github.cvc5.Kind.APPLY_UF;
import static io.github.cvc5.Kind.BITVECTOR_ADD;
import static io.github.cvc5.Kind.BITVECTOR_AND;
import static io.github.cvc5.Kind.BITVECTOR_ASHR;
import static io.github.cvc5.Kind.BITVECTOR_EXTRACT;
import static io.github.cvc5.Kind.BITVECTOR_LSHR;
import static io.github.cvc5.Kind.BITVECTOR_MULT;
import static io.github.cvc5.Kind.BITVECTOR_NEG;
import static io.github.cvc5.Kind.BITVECTOR_OR;
import static io.github.cvc5.Kind.BITVECTOR_SDIV;
import static io.github.cvc5.Kind.BITVECTOR_SGE;
import static io.github.cvc5.Kind.BITVECTOR_SGT;
import static io.github.cvc5.Kind.BITVECTOR_SHL;
import static io.github.cvc5.Kind.BITVECTOR_SIGN_EXTEND;
import static io.github.cvc5.Kind.BITVECTOR_SLE;
import static io.github.cvc5.Kind.BITVECTOR_SLT;
import static io.github.cvc5.Kind.BITVECTOR_SMOD;
import static io.github.cvc5.Kind.BITVECTOR_SREM;
import static io.github.cvc5.Kind.BITVECTOR_SUB;
import static io.github.cvc5.Kind.BITVECTOR_TO_NAT;
import static io.github.cvc5.Kind.BITVECTOR_UDIV;
import static io.github.cvc5.Kind.BITVECTOR_UGE;
import static io.github.cvc5.Kind.BITVECTOR_UGT;
import static io.github.cvc5.Kind.BITVECTOR_ULE;
import static io.github.cvc5.Kind.BITVECTOR_ULT;
import static io.github.cvc5.Kind.BITVECTOR_UREM;
import static io.github.cvc5.Kind.BITVECTOR_XOR;
import static io.github.cvc5.Kind.BITVECTOR_ZERO_EXTEND;
import static io.github.cvc5.Kind.DISTINCT;
import static io.github.cvc5.Kind.DIVISION;
import static io.github.cvc5.Kind.EQUAL;
import static io.github.cvc5.Kind.EXISTS;
import static io.github.cvc5.Kind.FLOATINGPOINT_ADD;
import static io.github.cvc5.Kind.FLOATINGPOINT_DIV;
import static io.github.cvc5.Kind.FLOATINGPOINT_EQ;
import static io.github.cvc5.Kind.FLOATINGPOINT_GEQ;
import static io.github.cvc5.Kind.FLOATINGPOINT_GT;
import static io.github.cvc5.Kind.FLOATINGPOINT_LEQ;
import static io.github.cvc5.Kind.FLOATINGPOINT_LT;
import static io.github.cvc5.Kind.FLOATINGPOINT_MULT;
import static io.github.cvc5.Kind.FLOATINGPOINT_NEG;
import static io.github.cvc5.Kind.FLOATINGPOINT_REM;
import static io.github.cvc5.Kind.FLOATINGPOINT_SUB;
import static io.github.cvc5.Kind.FLOATINGPOINT_TO_FP_FROM_FP;
import static io.github.cvc5.Kind.FLOATINGPOINT_TO_FP_FROM_SBV;
import static io.github.cvc5.Kind.FLOATINGPOINT_TO_SBV;
import static io.github.cvc5.Kind.FORALL;
import static io.github.cvc5.Kind.GEQ;
import static io.github.cvc5.Kind.GT;
import static io.github.cvc5.Kind.IMPLIES;
import static io.github.cvc5.Kind.INTS_MODULUS;
import static io.github.cvc5.Kind.INT_TO_BITVECTOR;
import static io.github.cvc5.Kind.ITE;
import static io.github.cvc5.Kind.LEQ;
import static io.github.cvc5.Kind.LT;
import static io.github.cvc5.Kind.MULT;
import static io.github.cvc5.Kind.NEG;
import static io.github.cvc5.Kind.NOT;
import static io.github.cvc5.Kind.OR;
import static io.github.cvc5.Kind.REGEXP_ALL;
import static io.github.cvc5.Kind.REGEXP_ALLCHAR;
import static io.github.cvc5.Kind.REGEXP_COMPLEMENT;
import static io.github.cvc5.Kind.REGEXP_CONCAT;
import static io.github.cvc5.Kind.REGEXP_INTER;
import static io.github.cvc5.Kind.REGEXP_LOOP;
import static io.github.cvc5.Kind.REGEXP_OPT;
import static io.github.cvc5.Kind.REGEXP_PLUS;
import static io.github.cvc5.Kind.REGEXP_RANGE;
import static io.github.cvc5.Kind.REGEXP_STAR;
import static io.github.cvc5.Kind.REGEXP_UNION;
import static io.github.cvc5.Kind.STRING_CHARAT;
import static io.github.cvc5.Kind.STRING_CONCAT;
import static io.github.cvc5.Kind.STRING_CONTAINS;
import static io.github.cvc5.Kind.STRING_FROM_INT;
import static io.github.cvc5.Kind.STRING_INDEXOF;
import static io.github.cvc5.Kind.STRING_IN_REGEXP;
import static io.github.cvc5.Kind.STRING_LENGTH;
import static io.github.cvc5.Kind.STRING_LEQ;
import static io.github.cvc5.Kind.STRING_LT;
import static io.github.cvc5.Kind.STRING_PREFIX;
import static io.github.cvc5.Kind.STRING_REPLACE;
import static io.github.cvc5.Kind.STRING_SUBSTR;
import static io.github.cvc5.Kind.STRING_SUFFIX;
import static io.github.cvc5.Kind.STRING_TO_CODE;
import static io.github.cvc5.Kind.STRING_TO_INT;
import static io.github.cvc5.Kind.STRING_TO_LOWER;
import static io.github.cvc5.Kind.STRING_TO_REGEXP;
import static io.github.cvc5.Kind.STRING_TO_UPPER;
import static io.github.cvc5.Kind.SUB;
import static io.github.cvc5.Kind.TO_INTEGER;
import static io.github.cvc5.Kind.TO_REAL;
import static io.github.cvc5.Kind.VARIABLE_LIST;
import static io.github.cvc5.Kind.XOR;
import static io.github.cvc5.RoundingMode.ROUND_NEAREST_TIES_TO_EVEN;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.BitvectorBooleanExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorComparator;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorNegation;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
import gov.nasa.jpf.constraints.expressions.RegExCompoundOperator;
import gov.nasa.jpf.constraints.expressions.RegexCompoundExpression;
import gov.nasa.jpf.constraints.expressions.RegexOperatorExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanOperator;
import gov.nasa.jpf.constraints.expressions.StringCompoundExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerOperator;
import gov.nasa.jpf.constraints.expressions.StringOperator;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.types.BVIntegerType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.ConcreteBVIntegerType;
import gov.nasa.jpf.constraints.types.ConcreteFloatingPointType;
import gov.nasa.jpf.constraints.types.NamedSort;
import gov.nasa.jpf.constraints.types.Type;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Op;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.tudoaqua.jconstraints.cvc5.exception.CVC5ConversionException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import org.apache.commons.math3.fraction.BigFraction;

public class CVC5ExpressionGenerator extends AbstractExpressionVisitor<Term, Term> {

  private final Solver em;
  private HashMap<Variable, Term> vars;
  private final HashMap<String, Term> boundedVars;
  private final HashMap<String, io.github.cvc5.Sort> declaredTypes;
  private final HashMap<Function<?>, Term> declaredFunctions;

  private final Sort doubleSort;
  private final Sort floatSort;

  private final Term defaultRoundingMode;

  public CVC5ExpressionGenerator(Solver emT) {
    vars = new HashMap<>();
    this.em = emT;
    try {
      doubleSort = em.mkFloatingPointSort(11, 53);
      floatSort = em.mkFloatingPointSort(8, 24);
    } catch (CVC5ApiException e) {
      throw new CVC5ConversionException(e);
    }
    declaredTypes = new HashMap<>();
    declaredFunctions = new HashMap<>();
    boundedVars = new HashMap<>();
    defaultRoundingMode = em.mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN);
  }

  public CVC5ExpressionGenerator(Solver emT, HashMap<Variable, Term> vars) {
    this(emT);
    this.vars = vars;
  }

  public Term generateExpression(Expression<Boolean> expression) {
    return visit(expression);
  }

  @Override
  public <E> Term visit(Variable<E> v, Term data) {
    if (vars.containsKey(v)) {
      return vars.get(v);
    } else if (boundedVars.containsKey(v.getName())) {
      return boundedVars.get(v.getName());
    } else {
      Term var = em.mkConst(mapToCVC5Sort(v.getType()), v.getName());
      vars.put(v, var);
      return var;
    }
  }

  @Override
  public <E> Term visit(Constant<E> c, Term data) {
    try {
      if (c.getType().equals(BuiltinTypes.BOOL)) {
        return em.mkBoolean((Boolean) c.getValue());
      } else if (c.getType().equals(BuiltinTypes.REAL)) {
        BigFraction bf = (BigFraction) c.getValue();
        return em.mkReal(bf.getNumerator().intValue(), bf.getDenominator().intValue());
      } else if (c.getType().equals(BuiltinTypes.SINT32)) {
        Constant<java.lang.Integer> intConst = (Constant<java.lang.Integer>) c;
        return em.mkBitVector(32, Integer.toBinaryString(intConst.getValue()), 2);
      } else if (c.getType().equals(BuiltinTypes.SINT64)) {
        Constant<Long> longConst = (Constant<Long>) c;
        return em.mkBitVector(64, Long.toBinaryString(longConst.getValue()), 2);
      } else if (c.getType().equals(BuiltinTypes.INTEGER)) {
        BigInteger bi = (BigInteger) c.getValue();
        return em.mkInteger(bi.longValue());
      } else if (c.getType().equals(BuiltinTypes.DOUBLE)) {
        double value = (Double) c.getValue();
        if (value == 0.0) {
          return em.mkFloatingPointPosZero(
              doubleSort.getFloatingPointExponentSize(),
              doubleSort.getFloatingPointSignificandSize());
        }

        long longValue = Double.doubleToLongBits(value);
        return em.mkFloatingPoint(
            doubleSort.getFloatingPointExponentSize(),
            doubleSort.getFloatingPointSignificandSize(),
            em.mkBitVector(64, longValue));
      } else if (c.getType().equals(BuiltinTypes.FLOAT)) {
        float value = (Float) c.getValue();
        if (value == 0.0f) {
          return em.mkFloatingPointPosZero(
              floatSort.getFloatingPointExponentSize(),
              floatSort.getFloatingPointSignificandSize());
        }
        int intValue = Float.floatToIntBits(value);
        return em.mkFloatingPoint(
            floatSort.getFloatingPointExponentSize(),
            floatSort.getFloatingPointSignificandSize(),
            em.mkBitVector(32, intValue));
      } else if (c.getType().equals(BuiltinTypes.STRING)) {
        String content = c.getValue().toString();
        return em.mkString(content);
      } else {
        throw new UnsupportedOperationException(
            "Cannot convert Constant: " + c.getType() + "with value: " + c.getValue());
      }
    } catch (CVC5ApiException e) {
      throw new CVC5ConversionException(e);
    }
  }

  @Override
  public Term visit(Negation n, Term data) {
    Term contained = visit(n.getNegated(), data);
    return contained.notTerm();
  }

  @Override
  public Term visit(NumericBooleanExpression n, Term data) {
    Term left = visit(n.getLeft(), data);
    Term right = visit(n.getRight(), data);

    boolean bvTypes = isBVType(n.getLeft(), n.getRight());
    boolean fpTypes = isFPType(n.getLeft(), n.getRight());
    boolean signed = isSigned(n.getLeft(), n.getRight());

    Kind kComparator = convertNumericComparator(n.getComparator(), bvTypes, fpTypes, signed);
    if (fpTypes) {
      if (kComparator == null && n.getComparator().equals(NumericComparator.NE)) {
        Term equals = em.mkTerm(FLOATINGPOINT_EQ, left, right);
        return em.mkTerm(NOT, equals);
      }
    }

    return em.mkTerm(kComparator, left, right);
  }

  @Override
  public <E> Term visit(NumericCompound<E> n, Term data) {
    Term left = visit(n.getLeft(), data);
    Term right = visit(n.getRight(), data);

    boolean bvTypes = isBVType(n.getLeft(), n.getRight());
    boolean fpTypes = isFPType(n.getLeft(), n.getRight());
    boolean signed = isSigned(n.getLeft(), n.getRight());

    Kind kOperator = convertNumericOperator(n.getOperator(), bvTypes, fpTypes, signed);

    if (fpTypes) {
      return em.mkTerm(kOperator, defaultRoundingMode, left, right);
    } else {
      return em.mkTerm(kOperator, left, right);
    }
  }

  @Override
  public Term visit(PropositionalCompound n, Term data) {
    Term left = visit(n.getLeft(), data);
    Term right = visit(n.getRight(), data);
    Term all;
    switch (n.getOperator()) {
      case AND:
        all = em.mkTerm(AND, left, right);
        break;
      case OR:
        all = em.mkTerm(OR, left, right);
        break;
      case XOR:
        all = em.mkTerm(XOR, left, right);
        break;
      case EQUIV:
        all = em.mkTerm(EQUAL, left, right);
        break;
      case IMPLY:
        all = em.mkTerm(IMPLIES, left, right);
        break;
      default:
        throw new UnsupportedOperationException("Cannot convert operator: " + n);
    }
    return all;
  }

  @Override
  public <E> Term visit(UnaryMinus<E> n, Term data) {
    Term negated = visit(n.getNegated());
    if (n.getNegated().getType() instanceof ConcreteBVIntegerType) {
      return em.mkTerm(BITVECTOR_NEG, negated);
    } else if (n.getNegated().getType() instanceof ConcreteFloatingPointType) {
      return em.mkTerm(FLOATINGPOINT_NEG, negated);
    } else {
      return em.mkTerm(NEG, negated);
    }
  }

  public Term visit(Function<?> f) {
    if (declaredFunctions.containsKey(f)) {
      return declaredFunctions.get(f);
    }
    Type<?>[] paramTypes = f.getParamTypes();
    Sort[] functionTypes = new Sort[paramTypes.length];
    for (int i = 0; i < paramTypes.length; i++) {
      functionTypes[i] = mapToCVC5Sort(paramTypes[i]);
    }
    Sort fType = em.mkFunctionSort(functionTypes, mapToCVC5Sort(f.getReturnType()));
    Term function = em.mkConst(fType, f.getName());
    declaredFunctions.put(f, function);
    return function;
  }

  @Override
  public <E> Term visit(FunctionExpression<E> f, Term data) {
    Expression<?>[] eArgs = f.getArgs();
    Term[] args = new Term[f.getArgs().length + 1];
    args[0] = visit(f.getFunction());
    for (int i = 0; i < eArgs.length; i++) {
      args[i + 1] = visit(eArgs[i], data);
    }
    return em.mkTerm(APPLY_UF, args);
  }

  @Override
  public <F, E> Term visit(CastExpression<F, E> cast, Term data) {
    Term casted = visit(cast.getCasted(), data);
    Op op = null;
    try {
      if (cast.getType().equals(BuiltinTypes.SINT32)
          && cast.getCasted().getType().equals(BuiltinTypes.INTEGER)) {
        op = em.mkOp(INT_TO_BITVECTOR, 32);
      } else if (cast.getType().equals(BuiltinTypes.SINT32)
          && cast.getCasted().getType().equals(BuiltinTypes.UINT16)) {
        op = em.mkOp(BITVECTOR_ZERO_EXTEND, 16);
      } else if (cast.getType().equals(BuiltinTypes.SINT32)
          && cast.getCasted().getType().equals(BuiltinTypes.SINT16)) {
        op = em.mkOp(BITVECTOR_SIGN_EXTEND, 16);
      } else if (cast.getType().equals(BuiltinTypes.SINT32)
          && cast.getCasted().getType().equals(BuiltinTypes.SINT8)) {
        op = em.mkOp(BITVECTOR_ZERO_EXTEND, 24);
      } else if (cast.getType().equals(BuiltinTypes.SINT32)
          && (cast.getCasted().getType().equals(BuiltinTypes.DOUBLE)
              || cast.getCasted().getType().equals(BuiltinTypes.FLOAT))) {
        op = em.mkOp(FLOATINGPOINT_TO_SBV, 32);
        return makeFPTerm(op, casted);
      } else if (cast.getType().equals(BuiltinTypes.SINT64)
          && (cast.getCasted().getType().equals(BuiltinTypes.DOUBLE)
              || cast.getCasted().getType().equals(BuiltinTypes.FLOAT))) {
        op = em.mkOp(FLOATINGPOINT_TO_SBV, 64);
        return makeFPTerm(op, casted);
      } else if (cast.getType().equals(BuiltinTypes.SINT64)
          && cast.getCasted().getType().equals(BuiltinTypes.SINT32)) {
        op = em.mkOp(BITVECTOR_SIGN_EXTEND, 32);
      } else if (cast.getType().equals(BuiltinTypes.UINT16)
          && cast.getCasted().getType() instanceof BVIntegerType) {
        op = em.mkOp(BITVECTOR_EXTRACT, 15, 0);
      } else if (cast.getType().equals(BuiltinTypes.SINT16)
          && cast.getCasted().getType().equals(BuiltinTypes.SINT32)) {
        op = em.mkOp(BITVECTOR_EXTRACT, 15, 0);
      } else if (cast.getType().equals(BuiltinTypes.SINT8)
          && cast.getCasted().getType() instanceof BVIntegerType) {
        op = em.mkOp(BITVECTOR_EXTRACT, 7, 0);
      } else if (cast.getType().equals(BuiltinTypes.INTEGER)
          && cast.getCasted().getType() instanceof BVIntegerType) {
        return em.mkTerm(BITVECTOR_TO_NAT, casted);
      } else if (cast.getType().equals(BuiltinTypes.INTEGER)
          && cast.getCasted().getType().equals(BuiltinTypes.REAL)) {
        return em.mkTerm(TO_INTEGER, casted);
      } else if (cast.getType().equals(BuiltinTypes.REAL)
          && cast.getCasted().getType().equals(BuiltinTypes.INTEGER)) {
        return em.mkTerm(TO_REAL, casted);
      } else if (cast.getType().equals(BuiltinTypes.DOUBLE)
          && (cast.getCasted().getType().equals(BuiltinTypes.SINT32)
              || cast.getCasted().getType().equals(BuiltinTypes.SINT64))) {
        op =
            em.mkOp(
                FLOATINGPOINT_TO_FP_FROM_SBV,
                doubleSort.getFloatingPointExponentSize(),
                doubleSort.getFloatingPointSignificandSize());
        return makeFPTerm(op, casted);
      } else if (cast.getType().equals(BuiltinTypes.DOUBLE)
          && (cast.getCasted().getType().equals(BuiltinTypes.FLOAT))) {
        op =
            em.mkOp(
                FLOATINGPOINT_TO_FP_FROM_FP,
                doubleSort.getFloatingPointExponentSize(),
                doubleSort.getFloatingPointSignificandSize());
        return makeFPTerm(op, casted);
      } else if (cast.getType().equals(BuiltinTypes.FLOAT)
          && (cast.getCasted().getType().equals(BuiltinTypes.DOUBLE))) {
        op =
            em.mkOp(
                FLOATINGPOINT_TO_FP_FROM_FP,
                floatSort.getFloatingPointExponentSize(),
                floatSort.getFloatingPointSignificandSize());
        return makeFPTerm(op, casted);
      } else if (cast.getType().equals(BuiltinTypes.FLOAT)
          && (cast.getCasted().getType().equals(BuiltinTypes.SINT32)
              || cast.getCasted().getType().equals(BuiltinTypes.SINT64))) {
        op =
            em.mkOp(
                FLOATINGPOINT_TO_FP_FROM_SBV,
                floatSort.getFloatingPointExponentSize(),
                floatSort.getFloatingPointSignificandSize());
        return makeFPTerm(op, casted);
      } else if (cast.getCasted() instanceof Constant) {
        if (cast.getType().equals(BuiltinTypes.INTEGER)) {
          return em.mkInteger(casted.getStringValue());
        }
      } else {
        throw new UnsupportedOperationException(
            String.format(
                "Cannot cast: %s to %s",
                cast.getCasted().getType().getName(), cast.getType().getName()));
      }
    } catch (CVC5ApiException e) {
      throw new CVC5ConversionException(e);
    }
    return em.mkTerm(op, casted);
  }

  @Override
  public <E> Term visit(IfThenElse<E> n, Term data) {
    Term condition = visit(n.getIf(), data);
    Term ifPart = visit(n.getThen(), data);
    Term elsePart = visit(n.getElse(), data);

    return em.mkTerm(ITE, condition, ifPart, elsePart);
  }

  @Override
  public <E> Term visit(BitvectorExpression<E> bv, Term data) {
    Term left = visit(bv.getLeft(), data);
    Term right = visit(bv.getRight(), data);
    Kind bvOperator = convertBVOperator(bv.getOperator());
    return em.mkTerm(bvOperator, left, right);
  }

  @Override
  public Term visit(BitvectorBooleanExpression bv, Term data) {
    Kind bvOperator = convertBitvectorComparator(bv.getComparator());
    Term left = visit(bv.getLeft(), data);
    Term right = visit(bv.getRight(), data);
    return em.mkTerm(bvOperator, left, right);
  }

  @Override
  public Term visit(LetExpression let, Term data) {
    Expression<?> e = let.flattenLetExpression();
    return visit(e, data);
  }

  @Override
  public Term visit(StringBooleanExpression n, Term data) {
    ArrayList<Term> exprs = new ArrayList<>();
    Expression<?>[] children = n.getChildren();
    Kind operator = convertStringBooleanOperator(n.getOperator());
    switch (n.getOperator()) {
      case PREFIXOF:
      case SUFFIXOF:
        return em.mkTerm(operator, visit(children[1], data), visit(children[0], data));
      default:
        for (Expression child : children) {
          exprs.add(visit(child, data));
        }
        return em.mkTerm(operator, exprs.toArray(new Term[0]));
    }
  }

  @Override
  public Term visit(StringIntegerExpression n, Term data) {
    Term[] exprs =
        Arrays.stream(n.getChildren()).map(child -> visit(child, data)).toArray(Term[]::new);
    Kind operator = convertStringIntegerOperator(n.getOperator());
    return em.mkTerm(operator, exprs);
  }

  @Override
  public Term visit(StringCompoundExpression n, Term data) {
    Term[] exprs =
        Arrays.stream(n.getChildren()).map(child -> visit(child, data)).toArray(Term[]::new);
    Kind operator = convertStringCompoundOperator(n.getOperator());
    return em.mkTerm(operator, exprs);
  }

  @Override
  public Term visit(RegExBooleanExpression n, Term data) {
    Term left = visit(n.getLeft());
    Term right = visit(n.getRight());
    return em.mkTerm(STRING_IN_REGEXP, left, right);
  }

  @Override
  public Term visit(RegexCompoundExpression n, Term data) {
    Term left = visit(n.getLeft());
    Term right = visit(n.getRight());
    Kind op = resolveRegexOperator(n.getOperator());
    return em.mkTerm(op, left, right);
  }

  private Kind resolveRegexOperator(RegExCompoundOperator op) {
    switch (op) {
      case CONCAT:
        return REGEXP_CONCAT;
      case UNION:
        return REGEXP_UNION;
      case INTERSECTION:
        return REGEXP_INTER;
      default:
        throw new UnsupportedOperationException("Don't know Operator: " + op);
    }
  }

  @Override
  public Term visit(RegexOperatorExpression n, Term data) {
    switch (n.getOperator()) {
      case KLEENESTAR:
        Term left = visit(n.getLeft(), data);
        return em.mkTerm(REGEXP_STAR, left);
      case KLEENEPLUS:
        left = visit(n.getLeft(), data);
        return em.mkTerm(REGEXP_PLUS, left);
      case LOOP:
        left = visit(n.getLeft(), data);
        try {
          return em.mkTerm(em.mkOp(REGEXP_LOOP, n.getLow(), n.getHigh()), left);
        } catch (CVC5ApiException e) {
          throw new CVC5ConversionException(e);
        }
      case RANGE:
        Term from = em.mkString(Character.toString(n.getCh1()));
        Term to = em.mkString(Character.toString(n.getCh2()));
        return em.mkTerm(REGEXP_RANGE, from, to);
      case OPTIONAL:
        left = visit(n.getLeft(), data);
        return em.mkTerm(REGEXP_OPT, left);
      case STRTORE:
        if (n.getS() != null) {
          left = em.mkString(n.getS().replace("\\", "\\u{5c}"), true);
        } else {
          left = visit(n.getLeft());
        }
        return em.mkTerm(STRING_TO_REGEXP, left);
      case ALLCHAR:
        return em.mkTerm(REGEXP_ALLCHAR);
      case ALL:
        return em.mkTerm(REGEXP_ALL);
      case COMPLEMENT:
        left = visit(n.getLeft(), data);
        return em.mkTerm(REGEXP_COMPLEMENT, left);
      case NOSTR:
        return em.mkRegexpNone();
      default:
        throw new UnsupportedOperationException();
    }
  }

  @Override
  public Term visit(QuantifierExpression q, Term data) {
    ArrayList<Term> vars = new ArrayList<>();
    for (Variable v : q.getBoundVariables()) {
      Term cvc4Var = em.mkVar(mapToCVC5Sort(v.getType()), v.getName());
      vars.add(cvc4Var);
      boundedVars.put(v.getName(), cvc4Var);
    }
    Term quantifiedVars = em.mkTerm(VARIABLE_LIST, vars.toArray(new Term[0]));
    Term body = visit(q.getBody(), data);

    for (Variable v : q.getBoundVariables()) {
      boundedVars.remove(v.getName());
    }

    switch (q.getQuantifier()) {
      case EXISTS:
        return em.mkTerm(EXISTS, quantifiedVars, body);
      case FORALL:
        return em.mkTerm(FORALL, quantifiedVars, body);
      default:
        throw new IllegalArgumentException("There are only two quantifiers");
    }
  }

  @Override
  public <E> Term visit(BitvectorNegation<E> n, Term data) {
    Term child = visit(n.getNegated(), data);
    return em.mkTerm(BITVECTOR_NEG, child);
  }

  public HashMap<Variable, Term> getVars() {
    return new HashMap<>(vars);
  }

  public void clearVars() {
    vars.clear();
  }

  private Sort mapToCVC5Sort(Type type) {
    if (type instanceof BuiltinTypes.RealType || type instanceof BuiltinTypes.BigDecimalType) {
      return em.getRealSort();
    } else if (type instanceof BuiltinTypes.BoolType) {
      return em.getBooleanSort();
    } else if (type instanceof BuiltinTypes.DoubleType) {
      return doubleSort;
    } else if (type instanceof BuiltinTypes.FloatType) {
      return floatSort;
    } else if (type instanceof BuiltinTypes.BigIntegerType) {
      return em.getIntegerSort();
    } else if (type instanceof BVIntegerType) {
      try {
        return em.mkBitVectorSort(((BVIntegerType<?>) type).getNumBits());
      } catch (CVC5ApiException e) {
        throw new CVC5ConversionException(e);
      }
    } else if (type.equals(BuiltinTypes.STRING)) {
      return em.getStringSort();
    } else if (type instanceof NamedSort) {
      if (declaredTypes.containsKey(type.getName())) {
        return declaredTypes.get(type.getName());
      } else {
        Sort t = em.mkUninterpretedSort(type.getName());
        declaredTypes.put(type.getName(), t);
        return t;
      }

    } else {
      throw new CVC5ConversionException("Cannot convert Type: " + type.getName());
    }
  }

  private Kind convertStringBooleanOperator(StringBooleanOperator operator) {
    switch (operator) {
      case EQUALS:
        return EQUAL;
      case CONTAINS:
        return STRING_CONTAINS;
      case PREFIXOF:
        return STRING_PREFIX;
      case SUFFIXOF:
        return STRING_SUFFIX;
      case LESSTHAN:
        return STRING_LT;
      case LESSTHANEQ:
        return STRING_LEQ;
      default:
        throw new UnsupportedOperationException("Cannot convert the Operator: " + operator);
    }
  }

  private Kind convertStringIntegerOperator(StringIntegerOperator operator) {
    switch (operator) {
      case INDEXOF:
        return STRING_INDEXOF;
      case TOINT:
        return STRING_TO_INT;
      case LENGTH:
        return STRING_LENGTH;
      case TOCODEPOINT:
        return STRING_TO_CODE;
      default:
        throw new UnsupportedOperationException("Cannot convert the Operator: " + operator);
    }
  }

  private Kind convertStringCompoundOperator(StringOperator operator) {
    switch (operator) {
      case AT:
        return STRING_CHARAT;
      case TOSTR:
        return STRING_FROM_INT;
      case CONCAT:
        return STRING_CONCAT;
      case SUBSTR:
        return STRING_SUBSTR;
      case REPLACE:
        return STRING_REPLACE;
      case TOLOWERCASE:
        return STRING_TO_LOWER;
      case TOUPPERCASE:
        return STRING_TO_UPPER;
      default:
        throw new UnsupportedOperationException(
            "Cannot convert StringCompoundOperator: " + operator);
    }
  }

  private Kind convertBVOperator(BitvectorOperator operator) {
    switch (operator) {
      case AND:
        return BITVECTOR_AND;
      case OR:
        return BITVECTOR_OR;
      case XOR:
        return BITVECTOR_XOR;
      case SHIFTL:
        return BITVECTOR_SHL;
      case SHIFTR:
        return BITVECTOR_LSHR;
      case SHIFTUR:
        return BITVECTOR_ASHR;
      case SUB:
        return BITVECTOR_SUB;
      case ADD:
        return BITVECTOR_ADD;
      case MUL:
        return BITVECTOR_MULT;
      case SDIV:
        return BITVECTOR_SDIV;
      case SREM:
        return BITVECTOR_SREM;
      case UDIV:
        return BITVECTOR_UDIV;
      case UREM:
        return BITVECTOR_UREM;
      default:
        throw new UnsupportedOperationException(
            "Cannot convert BitvectorOperator: " + operator + " yet.");
    }
  }

  private Kind convertNumericComparator(
      NumericComparator comparator, boolean byTypes, boolean fpTypes, boolean signed) {
    if (byTypes) {
      return convertNumericComparatorBV(comparator, signed);
    } else if (fpTypes) {
      return ConvertNumericComparatorFP(comparator);
    } else {
      return convertNumericComparatorNBV(comparator);
    }
  }

  private Kind ConvertNumericComparatorFP(NumericComparator comparator) {
    switch (comparator) {
      case EQ:
        return FLOATINGPOINT_EQ;
      case NE:
        return null;
      case LT:
        return FLOATINGPOINT_LT;
      case LE:
        return FLOATINGPOINT_LEQ;
      case GT:
        return FLOATINGPOINT_GT;
      case GE:
        return FLOATINGPOINT_GEQ;
      default:
        throw new UnsupportedOperationException("Cannot resolve comparator to FP type");
    }
  }

  private Kind convertNumericComparatorNBV(NumericComparator cmp) {
    switch (cmp) {
      case EQ:
        return EQUAL;
      case NE:
        return DISTINCT;
      case GE:
        return GEQ;
      case GT:
        return GT;
      case LE:
        return LEQ;
      case LT:
        return LT;
      default:
        throw new UnsupportedOperationException("Cannot convert NumericComparator: " + cmp);
    }
  }

  private Kind convertNumericComparatorBV(NumericComparator cmp, boolean signed) {
    switch (cmp) {
      case EQ:
        return EQUAL;
      case NE:
        return DISTINCT;
      case GE:
        if (signed) {
          return BITVECTOR_SGE;
        } else {
          return BITVECTOR_UGE;
        }
      case GT:
        if (signed) {
          return BITVECTOR_SGT;
        } else {
          return BITVECTOR_UGT;
        }
      case LE:
        if (signed) {
          return BITVECTOR_SLE;
        } else {
          return BITVECTOR_ULE;
        }
      case LT:
        if (signed) {
          return BITVECTOR_SLT;
        } else {
          return BITVECTOR_ULT;
        }
      default:
        throw new UnsupportedOperationException("Cannot convert NumericComparator: " + cmp);
    }
  }

  private Kind convertNumericOperator(
      NumericOperator operator, boolean bvTypes, boolean fpTypes, boolean signed) {
    if (bvTypes) {
      return convertBVNumericOperator(operator, signed);
    } else if (fpTypes) {
      return convertFPNumericOperator(operator);
    } else {
      return convertNormalNumericOperator(operator);
    }
  }

  private Kind convertNormalNumericOperator(NumericOperator operator) {
    switch (operator) {
      case PLUS:
        return ADD;
      case MINUS:
        return SUB;
      case REM:
      case MOD:
        return INTS_MODULUS;
      case MUL:
        return MULT;
      case DIV:
        return DIVISION;
      default:
        throw new UnsupportedOperationException("Cannot convert operator: " + operator);
    }
  }

  private Kind convertBVNumericOperator(NumericOperator operator, boolean signed) {
    switch (operator) {
      case DIV:
        if (signed) {
          return BITVECTOR_SDIV;
        } else {
          return BITVECTOR_UDIV;
        }
      case MUL:
        return BITVECTOR_MULT;
      case REM:
        if (signed) {
          return BITVECTOR_SREM;
        } else {
          return BITVECTOR_UREM;
        }
      case PLUS:
        return BITVECTOR_ADD;
      case MINUS:
        return BITVECTOR_SUB;
      case MOD:
        if (signed) {
          return BITVECTOR_SMOD;
        } else {
          return BITVECTOR_UREM;
        }
      default:
        throw new UnsupportedOperationException("Cannot convert operator: " + operator);
    }
  }

  private Kind convertFPNumericOperator(NumericOperator operator) {
    switch (operator) {
      case DIV:
        return FLOATINGPOINT_DIV;
      case MUL:
        return FLOATINGPOINT_MULT;
      case MINUS:
        return FLOATINGPOINT_SUB;
      case PLUS:
        return FLOATINGPOINT_ADD;
      case MOD:
      case REM:
        return FLOATINGPOINT_REM;
      default:
        throw new UnsupportedOperationException("Cannot convert: " + operator);
    }
  }

  private Kind convertBitvectorComparator(BitvectorComparator bc) {
    switch (bc) {
      case EQ:
        return EQUAL;
      case NE:
        return DISTINCT;
      case SGE:
        return BITVECTOR_SGE;
      case SGT:
        return BITVECTOR_SGT;
      case SLE:
        return BITVECTOR_SLE;
      case SLT:
        return BITVECTOR_SLT;
      case UGE:
        return BITVECTOR_UGE;
      case UGT:
        return BITVECTOR_UGT;
      case ULE:
        return BITVECTOR_ULE;
      case ULT:
        return BITVECTOR_ULT;
      default:
        throw new UnsupportedOperationException("Don't know this BitvectorComparator: " + bc);
    }
  }

  private boolean isBVType(Expression<?> left, Expression<?> right) {
    return left.getType() instanceof ConcreteBVIntegerType
        || right.getType() instanceof ConcreteBVIntegerType;
  }

  private boolean isFPType(Expression<?> left, Expression<?> right) {
    return left.getType() instanceof ConcreteFloatingPointType
        || right.getType() instanceof ConcreteFloatingPointType;
  }

  private boolean isSigned(Expression<?> left, Expression<?> right) {
    return left.getType() instanceof ConcreteBVIntegerType<?>
            && ((ConcreteBVIntegerType) left.getType()).isSigned()
        || right.getType() instanceof ConcreteBVIntegerType<?>
            && ((ConcreteBVIntegerType) right.getType()).isSigned();
  }

  private Term makeFPTerm(Op op, Term casted) {
    return em.mkTerm(op, defaultRoundingMode, casted);
  }
}
