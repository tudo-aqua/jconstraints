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

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.types.BitLimitedBVIntegerType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Term;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.apache.commons.math3.fraction.BigFractionFormat;

public class CVC5Solver extends ConstraintSolver implements UNSATCoreSolver {

  private static final Pattern fpPattern = Pattern.compile("fp#b(\\d)#b(\\d+)#b(\\d+)");
  private boolean isUnsatCoreTracking = false;

  private Solver smt;
  private CVC5ExpressionGenerator gen;

  public CVC5Solver() {
    smt = new Solver();
    gen = new CVC5ExpressionGenerator(smt);
    smt.setOption("produce-models", "true");
    smt.setOption("output-language", "smt");
    smt.setOption("strings-exp", "true");
    smt.setOption("seed", "1234");
    smt.setOption("sat-random-seed", "1234");
  }

  public CVC5Solver(Map<String, String> options) {
    this();
    for (Entry<String, String> e : options.entrySet()) {
      smt.setOption(e.getKey(), e.getValue());
    }
  }

  public static ConstraintSolver.Result convertCVC4Res(io.github.cvc5.Result res) {
    if (res.isSat()) {
      return Result.SAT;
    } else if (res.isUnsat()) {
      return Result.UNSAT;
    } else if (res.isUnknown()) {
      return Result.DONT_KNOW;
    }
    return Result.ERROR;
  }

  public static void getModel(Valuation val, HashMap<Variable, Term> vars, Solver smt)
      throws CVC5ApiException {
    if (val != null) {
      for (Map.Entry<Variable, Term> entry : vars.entrySet()) {
        Term value = smt.getValue(entry.getValue());
        if (!value.isNull()) {
          Kind k = value.getKind();
          String valueString = value.toString().replace("(", "").replace(")", "").replace(" ", "");
          if (Kind.CONST_RATIONAL.equals(k)) {
            if (entry.getKey().getType().equals(BuiltinTypes.INTEGER)) {
              val.setValue(entry.getKey(), new BigInteger(valueString));
            } else {
              val.setValue(
                  entry.getKey(), BigFractionFormat.getProperInstance().parse(valueString));
            }
          } else if (Kind.CONST_INTEGER.equals(k)) {
            val.setValue(entry.getKey(), new BigInteger(valueString));
          } else if (Kind.CONST_FLOATINGPOINT.equals(k)) {
            Matcher m = fpPattern.matcher(valueString);
            if (m.matches()) {
              String mattisse = m.group(3);
              String exponent = m.group(2);
              String sign = m.group(1);

              if (entry.getKey().getType().equals(BuiltinTypes.DOUBLE)) {
                long res = Long.parseUnsignedLong(sign + exponent + mattisse, 2);
                val.setValue(entry.getKey(), Double.longBitsToDouble(res));
              } else if (entry.getKey().getType().equals(BuiltinTypes.FLOAT)) {
                int res = Integer.parseUnsignedInt(sign + exponent + mattisse, 2);
                val.setValue(entry.getKey(), Float.intBitsToFloat(res));
              } else {
                throw new IllegalArgumentException(
                    "Don't know this floating point type: " + entry.getKey().getType().getName());
              }
            } else {
              throw new UnsupportedOperationException(
                  "Cannot parse the bit string: " + valueString);
            }
          } else if (Kind.CONST_BITVECTOR.equals(k)) {
            BigInteger bigValue =
                new BigInteger(valueString.replaceFirst("(?:(#b)|(0bin))", ""), 2);
            addRightBitvectorType(entry.getKey(), bigValue, val);
          } else if (Kind.CONST_BOOLEAN.equals(k)) {
            val.setValue(entry.getKey(), new Boolean(valueString).booleanValue());
          } else if (Kind.CONST_STRING.equals(k)) {
            valueString = value.toString();
            valueString =
                valueString.length() > 2
                    ? valueString.substring(1, valueString.length() - 1)
                    : valueString;
            valueString = resolveUnicode(valueString);
            val.setValue(entry.getKey(), valueString);
          } else if (Kind.UNINTERPRETED_SORT_VALUE.equals(k)) {
            valueString = valueString.split("_")[2];
            try {
              val.setParsedValue(entry.getKey(), valueString);
            } catch (ImpreciseRepresentationException e) {
              throw new IllegalArgumentException(
                  "Cannot handle the uninterpreted_constant value: "
                      + valueString
                      + " during model creation.");
            }
          } else {
            throw new IllegalArgumentException("Cannot parse the variable of the model");
          }
        }
      }
    }
  }

  private static String resolveUnicode(String toString) {
    toString = toString.replaceAll(Pattern.quote("u{5c}"), "");
    toString = toString.replaceAll(Pattern.quote("\"\""), "");
    return toString.replaceAll(Pattern.quote("\\u{0}"), "\0");
  }

  private static void addRightBitvectorType(Variable key, BigInteger bigValue, Valuation val) {
    if (key.getType().equals(BuiltinTypes.SINT32)) {
      val.setValue(key, bigValue.intValue());
    } else if (key.getType().equals(BuiltinTypes.SINT64)) {
      val.setValue(key, bigValue.longValue());
    } else if (key.getType().equals(BuiltinTypes.SINT8)) {
      val.setValue(key, bigValue.byteValueExact());
    } else if (key.getType().equals(BuiltinTypes.INTEGER)) {
      val.setValue(key, bigValue);
    } else if (key.getType() instanceof BitLimitedBVIntegerType) {
      if (bigValue.bitLength() <= ((BitLimitedBVIntegerType) key.getType()).getNumBits()) {
        val.setValue(key, bigValue);
      } else {
        throw new ArithmeticException("BigInteger out of specified bitrange");
      }
    } else {
      throw new UnsupportedOperationException(
          "Incomplete Type list. Missed: " + key.getType().getName());
    }
  }

  @Override
  public Result solve(Expression<Boolean> f, Valuation result) {
    gen.clearVars();
    Term expr = gen.generateExpression(f);
    try {
      io.github.cvc5.Result resCVC = smt.checkSatAssuming(expr);
      Result resJC = CVC5Solver.convertCVC4Res(resCVC);
      if (resCVC.isSat()) {
        getModel(result, gen.getVars(), smt);
      }
      return resJC;
    } catch (CVC5ApiException e) {
      throw new RuntimeException(e);
    }
  }

  @Override
  public Result isSatisfiable(Expression<Boolean> f) {
    io.github.cvc5.Result cvc5Res = smt.checkSatAssuming(gen.generateExpression(f));
    return CVC5Solver.convertCVC4Res(cvc5Res);
  }

  @Override
  public SolverContext createContext() {
    CVC5SolverContext ctx = new CVC5SolverContext();
    if (isUnsatCoreTracking) {
      ctx.enableUnsatTracking();
    }
    return ctx;
  }

  @Override
  public String getName() {
    return super.getName();
  }

  @Override
  public void enableUnsatTracking() {
    smt.setOption("produce-unsat-cores", "true");
    isUnsatCoreTracking = true;
  }

  @Override
  public void disableUnsatTracking() {
    smt.setOption("produce-unsat-cores", "false");
    isUnsatCoreTracking = false;
  }

  @Override
  public List<Expression<Boolean>> getUnsatCore() {
    throw new UnsupportedOperationException(
        "cvc5 supports only UNSAT Cores for the context in JConstraitns");
  }
}
