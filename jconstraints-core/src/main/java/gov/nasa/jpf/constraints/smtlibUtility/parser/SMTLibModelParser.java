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
import java.io.IOException;
import java.io.StringReader;
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

public class SMTLibModelParser {
  private static final Pattern p =
      Pattern.compile("^\\(model(?<value>.*)\\)(?:\\R?)$", Pattern.DOTALL);

  public static Valuation parseModel(String input, List<Variable<?>> vars)
      throws SMTLIBParserException {
    final SMT smt = new SMT();
    String value = extractValuePart(input);
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
          for (Variable<?> var : vars) {
            if (var.getName().equals(sym.value())) {
              val.setParsedValue(var, resolveUnicode(exprs.toString()));
            }
          }
        }
      }
    } catch (ParserException | IOException | ImpreciseRepresentationException e) {
      throw new SMTLIBParserException(e.getMessage());
    }
    return val;
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
}
