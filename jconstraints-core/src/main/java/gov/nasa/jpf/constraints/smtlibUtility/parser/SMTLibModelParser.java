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

package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import java.io.StringReader;
import java.math.BigInteger;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.smtlib.CharSequenceReader;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser;
import org.smtlib.IParser.ParserException;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.command.C_define_fun;
import org.smtlib.impl.SMTExpr.BinaryLiteral;
import org.smtlib.impl.SMTExpr.FcnExpr;

public class SMTLibModelParser {
  private static final Pattern p =
      Pattern.compile("^\\(model(?<value>.*)\\)(?:\\R?)$", Pattern.DOTALL);

  public static Valuation parseModel(String input, List<Variable<?>> vars)
      throws SMTLIBParserException {
    final SMT smt = new SMT();
    String value = extractValuePart(input);
    value = fixParenthesisPairs(value);
    Valuation val = new Valuation();
    final ISource toBeParsed =
        smt.smtConfig.smtFactory.createSource(
            new CharSequenceReader(new StringReader(value), input.length(), 100, 2), null);
    final IParser parser = smt.smtConfig.smtFactory.createParser(smt.smtConfig, toBeParsed);
    try {
      while (!parser.isEOD()) {
        ICommand cmd = parser.parseCommand();
        if (cmd instanceof C_define_fun) {
          C_define_fun fun = (C_define_fun) cmd;
          ISymbol sym = fun.symbol();
          IExpr exprs = fun.expression();
          String unicodeExprs = resolveUnicode(exprs.toString());
          for (Variable<?> var : vars) {
            if (var.getName().equals(sym.value())) {
              if (exprs instanceof BinaryLiteral) {
                if (var.getType().equals(BuiltinTypes.SINT32)) {
                  assert unicodeExprs.length() == 32;
                  BigInteger bi = new BigInteger(unicodeExprs, 2);
                  val.setValue((Variable<Integer>) var, bi.intValue());
                } else if (var.getType().equals(BuiltinTypes.SINT64)) {
                  assert unicodeExprs.length() == 64;
                  BigInteger bi = new BigInteger(unicodeExprs, 2);
                  val.setValue((Variable<Long>) var, bi.longValue());
                } else {
                  throw new IllegalArgumentException(
                      "Don't know, hot to parse this value into a model");
                }
              } else if (var.getType().equals(BuiltinTypes.DOUBLE)) {
                val.setValue((Variable<Double>) var, parseDoubleValue((FcnExpr) exprs));
              } else if (var.getType().equals(BuiltinTypes.FLOAT)) {
                val.setValue((Variable<Float>) var, parseFloatValue((FcnExpr) exprs));
              } else {
                val.setParsedValue(var, unicodeExprs);
              }
            }
          }
        }
      }
    } catch (ParserException | IOException | ImpreciseRepresentationException e) {
      throw new SMTLIBParserException(e.getMessage());
    }
    return val;
  }

  private static float parseFloatValue(FcnExpr exprs) {
    BigInteger bi = convertFPToBigInteger(exprs);
    return Float.intBitsToFloat(bi.intValue());
  }

  private static double parseDoubleValue(FcnExpr exprs) {
    BigInteger bi = convertFPToBigInteger(exprs);
    return Double.longBitsToDouble(bi.longValue());
  }

  private static BigInteger convertFPToBigInteger(FcnExpr exprs) {
    List args = exprs.args();
    String sign = resolveUnicode(args.get(0).toString());
    String exponent = resolveUnicode(args.get(1).toString());
    String mantissa = resolveUnicode(args.get(2).toString());
    return new BigInteger(sign + exponent + mantissa, 2);
  }

  private static String extractValuePart(String in) {
    Matcher m = p.matcher(in);
    String value = "";
    if (m.matches()) {
      value = m.group("value");
    }
    return value;
  }

  static String resolveUnicode(String toString) {
    toString = toString.replaceAll(Pattern.quote("\\u{7f}"), Character.toString((char) 127));
    toString = toString.replaceAll(Pattern.quote("u{5c}"), "");
    toString = toString.replaceAll(Pattern.quote("\\u{0}"), "\0");
    if (!toString.equals("\"\"")) {
      toString = toString.replaceAll("\"\"", "\"");
    }
    return toString;
  }

  static String fixParenthesisPairs(String value) {
    StringBuilder fixed = new StringBuilder();
    for (String v : value.split("\n")) {
      int closing_brackets = 0;
      int opening_brackets = 0;
      for (Character c : v.toCharArray()) {
        if (c == ')') {
          ++closing_brackets;
        } else if (c == '(') {
          ++opening_brackets;
        }
      }
      fixed.append(v);
      if (opening_brackets > closing_brackets) {
        for (int i = opening_brackets - closing_brackets; i > 0; --i) {
          fixed.append(")");
        }
      }
      fixed.append("\n");
    }
    return fixed.toString();
  }
}
