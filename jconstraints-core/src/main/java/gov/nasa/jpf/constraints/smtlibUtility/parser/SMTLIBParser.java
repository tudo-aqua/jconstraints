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

package gov.nasa.jpf.constraints.smtlibUtility.parser;

import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.BitVectorFunction;
import gov.nasa.jpf.constraints.expressions.BitvectorBooleanExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorComparator;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.ExpressionOperator;
import gov.nasa.jpf.constraints.expressions.FPComparator;
import gov.nasa.jpf.constraints.expressions.FPRoundingMode;
import gov.nasa.jpf.constraints.expressions.FloatingPointBooleanExpression;
import gov.nasa.jpf.constraints.expressions.FloatingPointFunction;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanOperator;
import gov.nasa.jpf.constraints.expressions.RegExCompoundOperator;
import gov.nasa.jpf.constraints.expressions.RegExOperator;
import gov.nasa.jpf.constraints.expressions.RegexCompoundExpression;
import gov.nasa.jpf.constraints.expressions.RegexOperatorExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanOperator;
import gov.nasa.jpf.constraints.expressions.StringCompoundExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerOperator;
import gov.nasa.jpf.constraints.expressions.StringOperator;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.*;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.IOException;
import java.io.StringReader;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.smtlib.CharSequenceReader;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser;
import org.smtlib.IParser.ParserException;
import org.smtlib.ISort;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.command.C_assert;
import org.smtlib.command.C_check_sat;
import org.smtlib.command.C_declare_fun;
import org.smtlib.command.C_exit;
import org.smtlib.command.C_get_model;
import org.smtlib.command.C_set_info;
import org.smtlib.command.C_set_logic;
import org.smtlib.command.C_set_option;
import org.smtlib.impl.SMTExpr;
import org.smtlib.impl.SMTExpr.FcnExpr;
import org.smtlib.impl.SMTExpr.HexLiteral;
import org.smtlib.impl.SMTExpr.Let;
import org.smtlib.impl.SMTExpr.ParameterizedIdentifier;
import org.smtlib.impl.SMTExpr.Symbol;
import org.smtlib.impl.Sort;

public class SMTLIBParser {

  private final Set<Variable> letContext;
  public SMTProblem problem;

  public SMTLIBParser() {
    problem = new SMTProblem();
    letContext = new HashSet<>();
  }

  public static SMTProblem parseSMTProgramFromFile(final String fileName)
      throws IOException, SMTLIBParserException {
    String input =
        Files.readAllLines(Paths.get(fileName)).stream()
            .reduce(
                "",
                (a, b) -> {
                  String processed = "";
                  if (!b.startsWith(";")) {
                    processed = b;
                    if (processed.contains(" ;")) {
                      processed = processed.split(" ;")[0];
                      processed += "\n";
                    } else if (processed.endsWith(";")) {
                      processed = processed.substring(0, processed.length() - 1);
                    }
                  }
                  return a + processed;
                });
    input = input.replaceAll(Character.toString((char) 127), "\\\\u{7F}");
    return parseSMTProgram(input);
  }

  public static SMTProblem parseSMTProgram(final String input)
      throws IOException, SMTLIBParserException {
    final SMT smt = new SMT();

    final ISource toBeParsed =
        smt.smtConfig.smtFactory.createSource(
            new CharSequenceReader(new StringReader(input), input.length(), 100, 2), null);
    final IParser parser = smt.smtConfig.smtFactory.createParser(smt.smtConfig, toBeParsed);
    final SMTLIBParser smtParser = new SMTLIBParser();
    try {
      boolean checkSatPassed = false;
      while (!parser.isEOD()) {
        ICommand cmd = parser.parseCommand();
        if (checkSatPassed) {
          if (!allowed(cmd)) {
            throw new SMTLIBParserNotSupportedException(
                "Check sat is only at the end of a smt problem allowed and might only be followed"
                    + " by(get-model), (exit) or another (check-sat)");
          }
        } else if (cmd instanceof C_declare_fun) {
          smtParser.processDeclareFun((C_declare_fun) cmd);
        } else if (cmd instanceof C_assert) {
          smtParser.processAssert((C_assert) cmd);
        } else if (cmd instanceof C_check_sat) {
          // It is okay, if check_sat is the last command in the chain, but it is just ignored.
          checkSatPassed = true;
        } else if (cmd instanceof C_set_info
            || cmd instanceof C_set_logic
            || cmd instanceof C_set_option) {
          // It is safe to ignore the info commands.
        } else {
          throw new SMTLIBParserNotSupportedException("Cannot parse the following command: " + cmd);
        }
      }
      return smtParser.problem;
    } catch (ParserException e) {
      throw new SMTLIBParserException(e.getMessage());
    }
  }

  private static boolean allowed(ICommand cmd) {
    return cmd instanceof C_exit || cmd instanceof C_get_model || cmd instanceof C_check_sat;
  }

  public Expression processAssert(final C_assert cmd) throws SMTLIBParserException {
    final Expression res = processExpression(cmd.expr());
    problem.addAssertion(res);
    return res;
  }

  public void processDeclareFun(final C_declare_fun cmd) throws SMTLIBParserException {
    if (cmd.argSorts().size() != 0) {
      throw new SMTLIBParserNotSupportedException(
          "Cannot convert the declared function, because argument size is not null. Might be"
              + " implemented in the future.");
    }
    if (!(cmd.resultSort() instanceof Sort.Application)) {
      throw new SMTLIBParserException("Could only convert type of type NamedSort.Application");
    }
    final Sort.Application application = (Sort.Application) cmd.resultSort();

    final Type<?> type;
    if (application.family().headSymbol().toString().equals("BitVec")) {
      if (((IParameterizedIdentifier) application.family()).numerals().size() > 1) {
        throw new SMTLIBParserException("To many Arguments in Type declaration.");
      } else {
        final int bits =
            ((IParameterizedIdentifier) application.family()).numerals().get(0).intValue();
        switch (bits) {
          case 8:
            type = BuiltinTypes.SINT8;
            break;
          case 16:
            type = BuiltinTypes.SINT16;
            break;
          case 32:
            type = BuiltinTypes.SINT32;
            break;
          case 64:
            type = BuiltinTypes.SINT64;
            break;
          default:
            type =
                new BitLimitedBVIntegerType(
                    ((IParameterizedIdentifier) application.family()).numerals().get(0).intValue(),
                    true);
            break;
        }
      }
    } else if (application.family().headSymbol().toString().equals("FloatingPoint")) {
      if (((IParameterizedIdentifier) application.family()).numerals().size() != 2) {
        throw new SMTLIBParserException("Wrong number of arguments in type declaration.");
      } else {
        final int exponentBits =
            ((IParameterizedIdentifier) application.family()).numerals().get(0).intValue();
        final int mantissaBits =
            ((IParameterizedIdentifier) application.family()).numerals().get(1).intValue();

        if (exponentBits == 8 && mantissaBits == 24) {
          type = BuiltinTypes.FLOAT;
        } else if (exponentBits == 11 && mantissaBits == 53) {
          type = BuiltinTypes.DOUBLE;
        } else {
          throw new SMTLIBParserException(
              "Unsupported layout of floating point type: "
                  + mantissaBits
                  + ":"
                  + exponentBits
                  + ".");
        }
      }
    } else {
      type = TypeMap.getType(application.toString());
    }
    if (type == null) {
      throw new SMTLIBParserExceptionInvalidMethodCall(
          "Could not resolve type declared in function: " + application.toString());
    }
    final Variable var = Variable.create(type, cmd.symbol().value());
    problem.addVariable(var);
  }

  private <E> Expression<E> processArgument(final IExpr arg) throws SMTLIBParserException {
    Expression<E> resolved = null;
    if (arg instanceof ISymbol) {
      resolved = resolveSymbol((ISymbol) arg);
    } else if (arg instanceof INumeral) {
      resolved = resolveNumeral((INumeral) arg);
    } else if (arg instanceof IDecimal) {
      resolved = resolveDecimal((IDecimal) arg);
    } else if (arg instanceof FcnExpr) {
      resolved = processFunctionExpression((FcnExpr) arg);
    } else if (arg instanceof Let) {
      resolved = processLetExpression((Let) arg);
    } else if (arg instanceof IStringLiteral) {
      resolved = resolveStringLiteral((IStringLiteral) arg);
    } else if (arg instanceof HexLiteral) {
      resolved = resolveHexLiteral((HexLiteral) arg);
    } else if (arg instanceof IExpr.IForall || arg instanceof IExpr.IExists) {
      resolved = processQuantifierExpression(arg);
    } else if (arg instanceof ParameterizedIdentifier) {
      resolved = processParametrizedIentifier((ParameterizedIdentifier) arg);
    } else if (arg instanceof SMTExpr.BinaryLiteral) {
      resolved = resolveBinaryLiteral((SMTExpr.BinaryLiteral) arg);
    } else {
      throw new SMTLIBParserNotSupportedException(
          "The arguments type is not supported: " + arg.getClass());
    }
    return successfulArgumentProcessing(resolved, arg);
  }

  private Expression processParametrizedIentifier(ParameterizedIdentifier arg)
      throws SMTLIBParserException {
    switch (arg.headSymbol().toString()) {
      case "NaN":
        switch (getFloatType(arg.numerals().get(0).intValue(), arg.numerals().get(1).intValue())) {
          case FLOAT:
            return Constant.create(BuiltinTypes.FLOAT, Float.NaN);
          case DOUBLE:
            return Constant.create(BuiltinTypes.DOUBLE, Double.NaN);
        }
      case "+oo":
        switch (getFloatType(arg.numerals().get(0).intValue(), arg.numerals().get(1).intValue())) {
          case FLOAT:
            return Constant.create(BuiltinTypes.FLOAT, Float.POSITIVE_INFINITY);
          case DOUBLE:
            return Constant.create(BuiltinTypes.DOUBLE, Double.POSITIVE_INFINITY);
        }
      case "-oo":
        switch (getFloatType(arg.numerals().get(0).intValue(), arg.numerals().get(1).intValue())) {
          case FLOAT:
            return Constant.create(BuiltinTypes.FLOAT, Float.NEGATIVE_INFINITY);
          case DOUBLE:
            return Constant.create(BuiltinTypes.DOUBLE, Double.NEGATIVE_INFINITY);
        }
      case "+zero":
        switch (getFloatType(arg.numerals().get(0).intValue(), arg.numerals().get(1).intValue())) {
          case FLOAT:
            return Constant.create(BuiltinTypes.FLOAT, +0.0f);
          case DOUBLE:
            return Constant.create(BuiltinTypes.DOUBLE, +0.0);
        }
      case "-zero":
        switch (getFloatType(arg.numerals().get(0).intValue(), arg.numerals().get(1).intValue())) {
          case FLOAT:
            return Constant.create(BuiltinTypes.FLOAT, -0.0f);
          case DOUBLE:
            return Constant.create(BuiltinTypes.DOUBLE, -0.0);
        }
    }
    throw new SMTLIBParserException("should not reach here.");
  }

  private enum FPType {
    FLOAT,
    DOUBLE
  };

  private FPType getFloatType(int exponentBits, int mantissaBits) throws SMTLIBParserException {
    if (exponentBits == 8 && mantissaBits == 24) {
      return FPType.FLOAT;
    } else if (exponentBits == 11 && mantissaBits == 53) {
      return FPType.DOUBLE;
    } else {
      throw new SMTLIBParserException(
          "Unsupported layout of floating point type: " + mantissaBits + ":" + exponentBits + ".");
    }
  }

  private Constant resolveHexLiteral(HexLiteral arg) {
    String value = arg.toString().replace("#x", "");
    if (value.length() == 2) {
      return Constant.create(BuiltinTypes.SINT8, Byte.parseByte(value, 16));
    } else if (value.length() == 8) {
      return Constant.create(BuiltinTypes.SINT32, Integer.parseUnsignedInt(value, 16));
    } else if (value.length() == 16) {
      return Constant.create(BuiltinTypes.SINT64, Long.parseUnsignedLong(value, 16));
    } else {
      throw new IllegalArgumentException("Wrong byte size in the hex value: #x" + value);
    }
  }

  private Constant resolveBinaryLiteral(SMTExpr.BinaryLiteral arg) {
    String value = arg.toString().replace("#b", "");
    if (value.length() == 8) {
      return Constant.create(BuiltinTypes.SINT8, Byte.parseByte(value, 2));
    } else if (value.length() == 32) {
      return Constant.create(BuiltinTypes.SINT32, Integer.parseUnsignedInt(value, 2));
    } else if (value.length() == 64) {
      return Constant.create(BuiltinTypes.SINT64, Long.parseUnsignedLong(value, 2));
    } else {
      throw new IllegalArgumentException("Wrong byte size in the hex value: #x" + value);
    }
  }

  private Expression processExpression(final IExpr expr) throws SMTLIBParserException {
    Expression res = null;
    if (expr instanceof FcnExpr) {
      res = processFunctionExpression((FcnExpr) expr);
    } else if (expr instanceof Let) {
      res = processLetExpression((Let) expr);
    } else if (expr instanceof Symbol) {
      res = resolveSymbol((ISymbol) expr);
    } else if (expr instanceof IExpr.IForall || expr instanceof IExpr.IExists) {
      res = processQuantifierExpression(expr);
    } else {
      throw new SMTLIBParserNotSupportedException(
          "Cannot parse the subexpression of type: " + expr.getClass());
    }
    return res;
  }

  private Expression processQuantifierExpression(final IExpr sExpr) throws SMTLIBParserException {
    final Quantifier quantifier;
    List<Variable<?>> boundVariables = new ArrayList<>();
    Expression<Boolean> body;

    if (sExpr instanceof IExpr.IForall) {
      quantifier = Quantifier.FORALL;
      List<IExpr.IDeclaration> parameters = ((IExpr.IForall) sExpr).parameters();
      if (!parameters.isEmpty()) {
        for (final IExpr.IDeclaration bound : parameters) {
          final String parameterValue = bound.parameter().value();
          ISort parameterSort = bound.sort();

          if (!(parameterSort instanceof Sort.Application)) {
            throw new SMTLIBParserException(
                "Could only convert type of type NamedSort.Application");
          }
          final Sort.Application application = (Sort.Application) parameterSort;

          final Type<?> type = TypeMap.getType(application.toString());
          if (type == null) {
            throw new SMTLIBParserExceptionInvalidMethodCall(
                "Could not resolve type declared in function: " + application.toString());
          } else {
            final Variable parameter = Variable.create(type, parameterValue);
            boundVariables.add(parameter);
            problem.addVariable(parameter);
          }
        }
      }
      IExpr bodyExpr = ((IExpr.IForall) sExpr).expr();
      body = processExpression(bodyExpr);
    } else { // sExpr instanceof IExpr.IExists
      quantifier = Quantifier.EXISTS;
      List<IExpr.IDeclaration> parameters = ((IExpr.IExists) sExpr).parameters();
      if (!parameters.isEmpty()) {
        for (final IExpr.IDeclaration bound : parameters) {
          final String parameterValue = bound.parameter().value();
          ISort parameterSort = bound.sort();

          if (!(parameterSort instanceof Sort.Application)) {
            throw new SMTLIBParserException(
                "Could only convert type of type NamedSort.Application");
          }
          final Sort.Application application = (Sort.Application) parameterSort;

          final Type<?> type = TypeMap.getType(application.toString());
          if (type == null) {
            throw new SMTLIBParserExceptionInvalidMethodCall(
                "Could not resolve type declared in function: " + application.toString());
          } else {
            final Variable parameter = Variable.create(type, parameterValue);
            boundVariables.add(parameter);
            problem.addVariable(parameter);
          }
        }
      }
      IExpr bodyExpr = ((IExpr.IExists) sExpr).expr();
      body = processExpression(bodyExpr);
    }
    return QuantifierExpression.create(quantifier, boundVariables, body);
  }

  private Expression processLetExpression(final Let sExpr) throws SMTLIBParserException {
    final List<Variable> parameters = new ArrayList();
    final Map<Variable, Expression> parameterValues = new HashMap<>();
    for (final IExpr.IBinding binding : sExpr.bindings()) {
      final Expression parameterValue = processExpression(binding.expr());
      final Variable parameter =
          Variable.create(parameterValue.getType(), binding.parameter().value());
      parameters.add(parameter);
      parameterValues.put(parameter, parameterValue);
    }
    letContext.addAll(parameters);
    final Expression mainValue = processExpression(sExpr.expr());
    letContext.removeAll(parameters);
    return LetExpression.create(parameters, parameterValues, mainValue);
  }

  private Expression processFunctionExpression(final FcnExpr sExpr) throws SMTLIBParserException {
    final String operatorStr = sExpr.head().headSymbol().value();
    final Queue<Expression> convertedArguments = new LinkedList<>();
    if (operatorStr.equals("fp")) {
      return parseFloatLiteral(sExpr);
    }
    for (final IExpr arg : sExpr.args()) {
      final Expression jExpr = processArgument(arg);
      convertedArguments.add(jExpr);
    }
    if (operatorStr.equals("re.loop")) {
      String tmp = sExpr.toString();
      Pattern p = Pattern.compile("[+-]?[0-9]+");
      Matcher m = p.matcher(tmp);
      SMT smt = new SMT();
      IExpr.IFactory efactory = smt.smtConfig.exprFactory;
      m.find();
      IExpr low = efactory.numeral(m.group());
      m.find();
      IExpr high = efactory.numeral(m.group());
      convertedArguments.add(processArgument(low));
      convertedArguments.add(processArgument(high));
    }
    Expression ret = null;
    if (operatorStr.equals("not")) {
      ret = createNegation(convertedArguments);
    } else if (operatorStr.equals("ite")) {
      ret = createITE(convertedArguments);
    } else if (operatorStr.equals("int2bv")) {
      ParameterizedIdentifier pi = (ParameterizedIdentifier) sExpr.head();
      ret = createCastToBV(convertedArguments, pi.numerals().get(0).intValue());
    } else if (operatorStr.equals("bv2nat") || operatorStr.equals("bv2int")) {
      ret = CastExpression.create(convertedArguments.poll(), BuiltinTypes.INTEGER);
    } else if (operatorStr.equals("sign_extend")
        || operatorStr.equals("zero_extend")
        || operatorStr.equals("extract")) {
      ret = createBVFunction(operatorStr, convertedArguments, sExpr);
    } else if (operatorStr.equals("distinct")) {
      ExpressionOperator eo = EQ;
      ret = createExpression(fixExpressionOperator(eo, convertedArguments), convertedArguments);
      ret = Negation.create(ret);
    } else if (operatorStr.equals("RNE")) {
      ret = FloatingPointFunction._rndMode(FPRoundingMode.RNE);
    } else if (operatorStr.equals("RNA")) {
      ret = FloatingPointFunction._rndMode(FPRoundingMode.RNA);
    } else if (operatorStr.equals("RTP")) {
      ret = FloatingPointFunction._rndMode(FPRoundingMode.RTP);
    } else if (operatorStr.equals("RTN")) {
      ret = FloatingPointFunction._rndMode(FPRoundingMode.RTN);
    } else if (operatorStr.equals("RTZ")) {
      ret = FloatingPointFunction._rndMode(FPRoundingMode.RTZ);
    } else if (operatorStr.startsWith("fp.") || operatorStr.equals("to_fp")) {
      ret = createFpFunction(operatorStr, convertedArguments, sExpr);
    } else {
      final ExpressionOperator operator =
          ExpressionOperator.fromString(
              FunctionOperatorMap.getjConstraintOperatorName(operatorStr));
      ret = createExpression(operator, convertedArguments);
    }
    return ret;
  }

  private Expression parseFloatLiteral(FcnExpr sExpr) {
    String sign = sExpr.args().get(0).toString();
    String exp = sExpr.args().get(1).toString();
    String mtsa = sExpr.args().get(2).toString();

    String bitString = sign + exp + mtsa;
    switch (bitString.length()) {
      case 32:
        if (exp.length() != 8) break;
        if (sign.equals("1") && mtsa.matches("0+")) {
          if (exp.matches("0+")) {
            return Constant.create(BuiltinTypes.FLOAT, -0.0f);
          }
          if (exp.matches("1+")) {
            return Constant.create(BuiltinTypes.FLOAT, Float.NEGATIVE_INFINITY);
          }
        }
        int ibits = Integer.parseUnsignedInt(bitString, 2);
        Float f = Float.intBitsToFloat(ibits);
        return Constant.create(BuiltinTypes.FLOAT, f);
      case 64:
        if (exp.length() != 11) break;
        if (sign.equals("1") && mtsa.matches("0+")) {
          if (exp.matches("0+")) {
            return Constant.create(BuiltinTypes.DOUBLE, -0.0);
          }
          if (exp.matches("1+")) {
            return Constant.create(BuiltinTypes.DOUBLE, Double.NEGATIVE_INFINITY);
          }
        }
        long lbits = Long.parseUnsignedLong(bitString, 2);
        Double d = Double.longBitsToDouble(lbits);
        return Constant.create(BuiltinTypes.DOUBLE, d);
    }

    throw new IllegalArgumentException(
        "fp format of width "
            + sign
            + " : "
            + exp
            + " : "
            + mtsa
            + " not supported by jconstraints");
  }

  private Expression createFpFunction(
      String operatorStr, Queue<Expression> convertedArguments, FcnExpr sExpr) {
    FPRoundingMode rndMode = null;
    switch (operatorStr) {
      case "fp.add":
        assert convertedArguments.size() == 3;
        rndMode = ((FloatingPointFunction) convertedArguments.poll()).getRmode();
        return FloatingPointFunction.fpadd(
            rndMode, convertedArguments.poll(), convertedArguments.poll());
      case "fp.sub":
        assert convertedArguments.size() == 3;
        rndMode = ((FloatingPointFunction) convertedArguments.poll()).getRmode();
        return FloatingPointFunction.fpsub(
            rndMode, convertedArguments.poll(), convertedArguments.poll());
      case "fp.mul":
        assert convertedArguments.size() == 3;
        rndMode = ((FloatingPointFunction) convertedArguments.poll()).getRmode();
        return FloatingPointFunction.fpmul(
            rndMode, convertedArguments.poll(), convertedArguments.poll());
      case "fp.div":
        assert convertedArguments.size() == 3;
        rndMode = ((FloatingPointFunction) convertedArguments.poll()).getRmode();
        return FloatingPointFunction.fpdiv(
            rndMode, convertedArguments.poll(), convertedArguments.poll());
      case "fp.fma":
        assert convertedArguments.size() == 4;
        rndMode = ((FloatingPointFunction) convertedArguments.poll()).getRmode();
        return FloatingPointFunction.fpfma(
            rndMode,
            convertedArguments.poll(),
            convertedArguments.poll(),
            convertedArguments.poll());
      case "fp.rem":
        assert convertedArguments.size() == 3;
        return FloatingPointFunction.fprem(convertedArguments.poll(), convertedArguments.poll());
      case "fp.neg":
        return FloatingPointFunction.fpneg(convertedArguments.poll());
      case "fp.abs":
        return FloatingPointFunction.fpabs(convertedArguments.poll());
      case "fp.sqrt":
        assert convertedArguments.size() == 2;
        rndMode = ((FloatingPointFunction) convertedArguments.poll()).getRmode();
        return FloatingPointFunction.fpsqrt(rndMode, convertedArguments.poll());
      case "fp.roundToIntegral":
        assert convertedArguments.size() == 2;
        rndMode = ((FloatingPointFunction) convertedArguments.poll()).getRmode();
        return FloatingPointFunction.fpRoundToIntegral(rndMode, convertedArguments.poll());
      case "fp.eq":
        return new FloatingPointBooleanExpression(
            FPComparator.FPEQ, convertedArguments.toArray(new Expression[] {}));
      case "fp.leq":
        return new FloatingPointBooleanExpression(
            FPComparator.FPLE, convertedArguments.toArray(new Expression[] {}));
      case "fp.geq":
        return new FloatingPointBooleanExpression(
            FPComparator.FPGE, convertedArguments.toArray(new Expression[] {}));
      case "fp.lt":
        return new FloatingPointBooleanExpression(
            FPComparator.FPLT, convertedArguments.toArray(new Expression[] {}));
      case "fp.gt":
        return new FloatingPointBooleanExpression(
            FPComparator.FPGT, convertedArguments.toArray(new Expression[] {}));
      case "fp.min":
        assert convertedArguments.size() == 2;
        return FloatingPointFunction.fp_min(convertedArguments.poll(), convertedArguments.poll());
      case "fp.max":
        assert convertedArguments.size() == 2;
        return FloatingPointFunction.fp_max(convertedArguments.poll(), convertedArguments.poll());
      case "fp.isNormal":
        assert convertedArguments.size() == 1;
        return new FloatingPointBooleanExpression(
            FPComparator.FP_IS_NORMAL, convertedArguments.poll());
      case "fp.isSubnormal":
        assert convertedArguments.size() == 1;
        return new FloatingPointBooleanExpression(
            FPComparator.FP_IS_SUBNORMAL, convertedArguments.poll());
      case "fp.isZero":
        assert convertedArguments.size() == 1;
        return new FloatingPointBooleanExpression(
            FPComparator.FP_IS_ZERO, convertedArguments.poll());
      case "fp.isNaN":
        assert convertedArguments.size() == 1;
        return new FloatingPointBooleanExpression(
            FPComparator.FP_IS_NAN, convertedArguments.poll());
      case "fp.isPositive":
        assert convertedArguments.size() == 1;
        return new FloatingPointBooleanExpression(
            FPComparator.FP_IS_POSITIVE, convertedArguments.poll());
      case "fp.isNegative":
        assert convertedArguments.size() == 1;
        return new FloatingPointBooleanExpression(
            FPComparator.FP_IS_NEGATIVE, convertedArguments.poll());
      case "fp.to_sbv":
        rndMode = ((FloatingPointFunction) convertedArguments.poll()).getRmode();
        ParameterizedIdentifier pi = (ParameterizedIdentifier) sExpr.head();
        return FloatingPointFunction.tosbv(
            rndMode, convertedArguments.poll(), pi.numerals().get(0).intValue());
      case "fp.to_ubv":
        rndMode = ((FloatingPointFunction) convertedArguments.poll()).getRmode();
        ParameterizedIdentifier pi3 = (ParameterizedIdentifier) sExpr.head();
        return FloatingPointFunction.toubv(
            rndMode, convertedArguments.poll(), pi3.numerals().get(0).intValue());
      case "fp.to_real":
        return FloatingPointFunction.toreal(convertedArguments.poll());
      case "to_fp":
        ParameterizedIdentifier pi2 = (ParameterizedIdentifier) sExpr.head();
        int ebits = pi2.numerals().get(0).intValue();
        int mbits = pi2.numerals().get(1).intValue();
        Expression peek = convertedArguments.peek();
        if (peek instanceof FloatingPointFunction) {
          // rounding mode ...
          FloatingPointFunction _rmode = (FloatingPointFunction) peek;
          assert _rmode.getFunction().equals(FloatingPointFunction.FPFCT._FP_RND);
          convertedArguments.poll();
          rndMode = _rmode.getRmode();
          // case analysis
          Expression arg = convertedArguments.poll();
          if (arg.getType() instanceof FloatingPointType) {
            return FloatingPointFunction.tofpFromFp(rndMode, arg, mbits, ebits);
          } else if (arg.getType() instanceof BVIntegerType) {
            return FloatingPointFunction.tofpFromBV(rndMode, arg, mbits, ebits);
          }
          if (arg.getType() instanceof RealType) {
            return FloatingPointFunction.tofpFromReal(rndMode, arg, mbits, ebits);
          }
        } else {
          // no rounding mode: from bitstring!
          return FloatingPointFunction.tofpFromBitstring(convertedArguments.poll(), mbits, ebits);
        }
        // fallthrough to default
      default:
        throw new IllegalArgumentException("Unsupported fp function: " + operatorStr);
    }
  }

  private Expression createBVFunction(
      String operatorStr, Queue<Expression> convertedArguments, FcnExpr sExpr) {
    ParameterizedIdentifier pi = (ParameterizedIdentifier) sExpr.head();
    switch (operatorStr) {
      case "sign_extend":
        return BitVectorFunction.signExtend(
            pi.numerals().get(0).intValue(), convertedArguments.poll());
      case "zero_extend":
        return BitVectorFunction.zeroExtend(
            pi.numerals().get(0).intValue(), convertedArguments.poll());
      case "extract":
        return BitVectorFunction.extract(
            pi.numerals().get(0).intValue(),
            pi.numerals().get(1).intValue(),
            convertedArguments.poll());
      default:
        throw new IllegalArgumentException("Unsupported bv function: " + operatorStr);
    }
  }

  private Expression createCastToBV(Queue<Expression> convertedArguments, int bitSize) {
    if (bitSize == 8) {
      return CastExpression.create(convertedArguments.poll(), BuiltinTypes.SINT8);
    } else if (bitSize == 16) {
      return CastExpression.create(convertedArguments.poll(), BuiltinTypes.SINT16);
    } else if (bitSize == 32) {
      return CastExpression.create(convertedArguments.poll(), BuiltinTypes.SINT32);
    } else if (bitSize == 64) {
      return CastExpression.create(convertedArguments.poll(), BuiltinTypes.SINT64);
    } else {
      throw new IllegalArgumentException("Cannot cast to bitSize: " + bitSize);
    }
  }

  private Negation createNegation(final Queue<Expression> arguments) throws SMTLIBParserException {
    if (arguments.size() == 1) {
      return Negation.create(arguments.poll());
    } else {
      throw new SMTLIBParserException("Cannot use more than one Argument in a Negation Expr");
    }
  }

  private IfThenElse createITE(final Queue<Expression> arguments) throws SMTLIBParserException {
    if (arguments.size() == 3) {
      return IfThenElse.create(arguments.poll(), arguments.poll(), arguments.poll());
    } else {
      throw new SMTLIBParserException(
          "Cannot convert ite-Expr with anything else than three arguments");
    }
  }

  private Expression createExpression(
      final ExpressionOperator operator, final Queue<Expression> arguments)
      throws SMTLIBParserNotSupportedException, SMTLIBParserExceptionInvalidMethodCall {

    checkOperatorNotNull(operator);
    checkImpliesOperatorRequirements(operator, arguments);

    final ExpressionOperator newOperator = fixExpressionOperator(operator, arguments);
    if (!(newOperator instanceof StringBooleanOperator
        || newOperator instanceof StringIntegerOperator
        || newOperator instanceof StringOperator
        || newOperator instanceof RegExCompoundOperator
        || newOperator instanceof RegExOperator
        || newOperator instanceof RegExBooleanOperator)) {
      Expression firstExpr = arguments.poll();
      Expression finalExpr = firstExpr;
      if (arguments.peek() == null) {
        if (newOperator == NumericOperator.MINUS && firstExpr != null) {
          finalExpr = UnaryMinus.create(firstExpr);
        } else if (newOperator == LogicalOperator.OR || newOperator == LogicalOperator.AND) {
          // We can safely drop them, if they have only one child;
        } else {
          arguments.add(firstExpr);
          throw new SMTLIBParserExceptionInvalidMethodCall(
              "It is strict required, that an operator "
                  + "is "
                  + "passed together with at least two "
                  + "arguments in the "
                  + "queue"
                  + ".\n"
                  + "This call got passed "
                  + "operator: "
                  + operator
                  + " arguments: "
                  + arguments);
        }
      }
      while (arguments.peek() != null) {
        final Expression next = arguments.poll();

        Tuple<Expression, Expression> t = equalizeTypes(finalExpr, next);
        if (newOperator instanceof NumericOperator) {
          finalExpr = NumericCompound.create(t.left, (NumericOperator) newOperator, t.right);
        } else if (newOperator instanceof LogicalOperator) {
          finalExpr = PropositionalCompound.create(t.left, (LogicalOperator) newOperator, t.right);
        } else if (newOperator instanceof BitvectorOperator) {
          finalExpr = BitvectorExpression.create(t.left, (BitvectorOperator) newOperator, t.right);
        } else if (newOperator instanceof NumericComparator) {
          finalExpr =
              NumericBooleanExpression.create(t.left, (NumericComparator) newOperator, t.right);
        } else if (newOperator instanceof BitvectorComparator) {
          finalExpr =
              BitvectorBooleanExpression.create(t.left, (BitvectorComparator) newOperator, t.right);
        } else if (newOperator instanceof FPComparator) {
          finalExpr =
              new FloatingPointBooleanExpression((FPComparator) newOperator, t.left, t.right);
        }
      }
      return finalExpr;
    } else if (newOperator instanceof StringOperator) {
      switch ((StringOperator) newOperator) {
        case AT:
          return StringCompoundExpression.createAt(arguments.poll(), arguments.poll());
        case CONCAT:
          Expression<?> tmpexpr[] = new Expression<?>[arguments.size()];
          tmpexpr[0] = arguments.poll();
          tmpexpr[1] = arguments.poll();
          for (int i = 2; i < tmpexpr.length; i++) {
            tmpexpr[i] = arguments.poll();
          }
          return StringCompoundExpression.createConcat(tmpexpr);
        case REPLACE:
          return StringCompoundExpression.createReplace(
              arguments.poll(), arguments.poll(), arguments.poll());
        case REPLACEALL:
          return StringCompoundExpression.createReplaceAll(
              arguments.poll(), arguments.poll(), arguments.poll());
        case SUBSTR:
          return StringCompoundExpression.createSubstring(
              arguments.poll(), arguments.poll(), arguments.poll());
        case TOSTR:
          return StringCompoundExpression.createToString(arguments.poll());
        case TOLOWERCASE:
          return StringCompoundExpression.createToLower(arguments.poll());
        case TOUPPERCASE:
          return StringCompoundExpression.createToUpper(arguments.poll());
        default:
          throw new IllegalArgumentException("Unknown StringCompoundOperator");
      }
    } else if (newOperator instanceof StringBooleanOperator) {
      switch ((StringBooleanOperator) newOperator) {
        case CONTAINS:
          return StringBooleanExpression.createContains(arguments.poll(), arguments.poll());
        case EQUALS:
          return processEquals(arguments.poll(), arguments.poll());
        case PREFIXOF:
          Expression prefix = arguments.poll();
          return StringBooleanExpression.createPrefixOf(arguments.poll(), prefix);
        case SUFFIXOF:
          Expression suffix = arguments.poll();
          return StringBooleanExpression.createSuffixOf(arguments.poll(), suffix);
        case LESSTHAN:
          return StringBooleanExpression.createLT(arguments.poll(), arguments.poll());
        case LESSTHANEQ:
          return StringBooleanExpression.createLTEQ(arguments.poll(), arguments.poll());

        default:
          throw new IllegalArgumentException("Unknown StringBooleanOperator: " + newOperator);
      }
    } else if (newOperator instanceof StringIntegerOperator) {
      switch ((StringIntegerOperator) newOperator) {
        case INDEXOF:
          if (arguments.size() == 0) {
            return StringIntegerExpression.createIndexOf(arguments.poll(), arguments.poll());
          } else {
            return StringIntegerExpression.createIndexOf(
                arguments.poll(), arguments.poll(), arguments.poll());
          }
        case LENGTH:
          return StringIntegerExpression.createLength(arguments.poll());
        case TOINT:
          return StringIntegerExpression.createToInt(arguments.poll());
        case TOCODEPOINT:
          return StringIntegerExpression.createToCodePoint(arguments.poll());
        case FROMCODEPOINT:
          return StringIntegerExpression.createFromCodePoint(arguments.poll());
        default:
          throw new IllegalArgumentException("Unknown StringIntegerOperator: " + newOperator);
      }
    } else if (newOperator instanceof RegExOperator) {
      switch ((RegExOperator) newOperator) {
        case ALLCHAR:
          return RegexOperatorExpression.createAllChar();
        case KLEENEPLUS:
          return RegexOperatorExpression.createKleenePlus(arguments.poll());
        case KLEENESTAR:
          return RegexOperatorExpression.createKleeneStar(arguments.poll());
        case LOOP:
          Expression re = arguments.poll();
          Constant lo = (Constant) arguments.poll();
          BigInteger lowLoop = (BigInteger) lo.getValue();

          if (arguments.peek() != null) {
            Constant hi = (Constant) arguments.poll();
            BigInteger highLoop = (BigInteger) hi.getValue();
            return RegexOperatorExpression.createLoop(re, lowLoop.intValue(), highLoop.intValue());
          }
          return RegexOperatorExpression.createLoop(re, (int) lo.getValue());
        case NOSTR:
          return RegexOperatorExpression.createNoChar();
        case OPTIONAL:
          return RegexOperatorExpression.createOptional(arguments.poll());
        case RANGE:
          Constant loR = (Constant) arguments.poll();
          Constant hiR = (Constant) arguments.poll();
          String l = (String) loR.getValue();
          String h = (String) hiR.getValue();
          char low = l.charAt(0);
          char high = h.charAt(0);
          return RegexOperatorExpression.createRange(low, high);
        case STRTORE:
          Expression e = arguments.poll();
          return RegexOperatorExpression.createStrToRe(e);
        default:
          throw new UnsupportedOperationException("Unknown RegexOperator: " + newOperator);
      }
    } else if (newOperator instanceof RegExCompoundOperator) {
      return convertRegExCompundOperator(newOperator, arguments);
    } else if (newOperator instanceof RegExBooleanOperator) {
      switch ((RegExBooleanOperator) newOperator) {
        case STRINRE:
          return RegExBooleanExpression.create(arguments.poll(), arguments.poll());
        default:
          throw new UnsupportedOperationException("Unknown RegexBooleanOperator: " + newOperator);
      }
    } else {
      throw new SMTLIBParserNotSupportedException(
          "Cannot convert the following operator class: " + operator.getClass());
    }
  }

  private Expression processEquals(Expression left, Expression right) {
    if (left.getType().equals(BuiltinTypes.STRING)) {
      return StringBooleanExpression.createEquals(left, right);
    } else if (left.getType().equals(BuiltinTypes.BOOL)) {
      return PropositionalCompound.create(left, LogicalOperator.EQUIV, right);
    } else if (left.getType() instanceof NumericType) {
      return NumericBooleanExpression.create(left, EQ, right);
    } else {
      throw new IllegalArgumentException(
          "Unknown StringBooleanOperator arguments: " + left + " " + right);
    }
  }

  private Expression convertRegExCompundOperator(
      ExpressionOperator newOperator, Queue<Expression> arguments) {
    switch ((RegExCompoundOperator) newOperator) {
      case CONCAT:
        Expression<?> tmpexpr[] = new Expression<?>[arguments.size()];
        tmpexpr[0] = arguments.poll();
        tmpexpr[1] = arguments.poll();
        for (int i = 2; i < tmpexpr.length; i++) {
          tmpexpr[i] = arguments.poll();
        }
        return RegexCompoundExpression.createConcat(tmpexpr);
      case INTERSECTION:
        return RegexCompoundExpression.createIntersection(arguments.poll(), arguments.poll());
      case UNION:
        RegexCompoundExpression rce =
            RegexCompoundExpression.createUnion(arguments.poll(), arguments.poll());
        while (!arguments.isEmpty()) {
          rce = RegexCompoundExpression.createUnion(rce, arguments.poll());
        }
        return rce;
      default:
        throw new UnsupportedOperationException("Unknown RegexCompoundOperator: " + newOperator);
    }
  }

  private Constant resolveDecimal(final IDecimal decimal) {
    return Constant.create(BuiltinTypes.DECIMAL, decimal.value());
  }

  private <L, R> Tuple<L, R> equalizeTypes(final Expression left, final Expression right)
      throws SMTLIBParserExceptionInvalidMethodCall {
    if (left.getType() == right.getType()) {
      return new Tuple(left, right);
    } else if (left.getType() instanceof BVIntegerType<?>
        && right.getType() instanceof BVIntegerType<?>
        && ((BVIntegerType<?>) (left.getType())).getNumBits()
            == ((BVIntegerType<?>) (right.getType())).getNumBits()) {
      return new Tuple(left, right);
    } else if (left instanceof UnaryMinus && right instanceof UnaryMinus) {
      throw new SMTLIBParserExceptionInvalidMethodCall(
          "Cannot equialize Types for two unary minus expressions");
    } else if ((left instanceof Constant
            || (left instanceof UnaryMinus && ((UnaryMinus) left).getNegated() instanceof Constant))
        && BuiltinTypes.isBuiltinType(right.getType())) {
      final Expression constant = convertTypeConstOrMinusConst(right.getType(), left);
      return new Tuple(constant, right);
    } else if ((right instanceof Constant
            || right instanceof UnaryMinus && ((UnaryMinus) right).getNegated() instanceof Constant)
        && BuiltinTypes.isBuiltinType(left.getType())) {
      final Expression constant = convertTypeConstOrMinusConst(left.getType(), right);
      return new Tuple(left, constant);
    } else {
      Expression righCast = right.as(left.getType());
      if (righCast != null) {
        return new Tuple(left, right);
      }
      Expression leftCast = left.as(right.getType());
      if (leftCast != null) {
        return new Tuple(leftCast, right);
      }
      throw new SMTLIBParserExceptionInvalidMethodCall(
          "The expressions are not equal, but they are also not a constant and another BuiltIn "
              + "expression type which might easily be type casted. left: "
              + left.getType()
              + " and right: "
              + right.getType());
    }
  }

  private Expression convertTypeConstOrMinusConst(final Type type, final Expression expr)
      throws SMTLIBParserExceptionInvalidMethodCall {
    if (expr instanceof UnaryMinus) {
      return convertUnaryMinus(type, (UnaryMinus) expr);
    } else if (expr instanceof Constant) {
      return Constant.createCasted(type, (Constant) expr);
    } else {
      throw new SMTLIBParserExceptionInvalidMethodCall(
          "Expected a Constant or Unary Expression, but got" + expr.getClass());
    }
  }

  private UnaryMinus convertUnaryMinus(final Type type, final UnaryMinus unary) {
    return UnaryMinus.create(Constant.createCasted(type, (Constant) unary.getNegated()));
  }

  private Constant resolveNumeral(final INumeral numeral) {
    return Constant.create(BuiltinTypes.INTEGER, numeral.value());
  }

  private Constant resolveStringLiteral(final IStringLiteral stringliteral) {
    String value = stringliteral.value();
    if (value.startsWith("\"") && value.endsWith("\"") && value.length() > 1) {
      value = value.substring(1, value.length() - 1);
    }
    return Constant.create(BuiltinTypes.STRING, value, true);
  }

  private Expression resolveSymbol(final ISymbol symbol)
      throws SMTLIBParserExceptionInvalidMethodCall, SMTLIBParserNotSupportedException {
    if (symbol.value().equals("RoundingMode")) {
      return FPRoundingMode.ROUNDING_MODE_SYMBOL;
    }
    if (symbol.value().equals("re.nostr")) {
      return createExpression(RegExOperator.NOSTR, new LinkedList<Expression>());
    }
    if (symbol.value().equals("re.allchar")) {
      return createExpression(RegExOperator.ALLCHAR, new LinkedList<Expression>());
    }
    if (symbol.value().equalsIgnoreCase("true")) {
      return ExpressionUtil.TRUE;
    }
    if (symbol.value().equalsIgnoreCase("false")) {
      return ExpressionUtil.FALSE;
    }
    for (final Variable var : problem.variables) {
      if (var.getName().equals(symbol.value())) {
        return var;
      }
    }

    for (final Variable parameter : letContext) {
      if (parameter.getName().equals(symbol.value())) {
        return parameter;
      }
    }
    if (symbol.value().matches("-(\\d)+")) {
      return Constant.create(BuiltinTypes.INTEGER, new BigInteger(symbol.value()));
    }

    throw new SMTLIBParserExceptionInvalidMethodCall("Cannot parse Symbol: " + symbol);
  }

  private <E> Expression<E> successfulArgumentProcessing(final Expression<E> expr, final IExpr arg)
      throws SMTLIBParserException {
    if (expr == null) {
      throw new SMTLIBParserException("Cannot process the following argument: " + arg);
    }
    return expr;
  }

  private boolean checkOperatorNotNull(final ExpressionOperator operator)
      throws SMTLIBParserExceptionInvalidMethodCall {
    if (operator == null) {
      throw new SMTLIBParserExceptionInvalidMethodCall(
          "Operator is null. Cannot create Operator dependent Expression!");
    }
    return true;
  }

  private final ExpressionOperator fixExpressionOperator(
      final ExpressionOperator operator, final Queue<Expression> arguments) {
    final Queue<Expression> tmp = new LinkedList<Expression>(arguments);
    final StringBooleanOperator newOperator = StringBooleanOperator.EQUALS;

    if (operator.equals(EQ)) {
      Expression left = tmp.poll();
      Expression right = tmp.poll();
      if (left instanceof StringBooleanExpression
          || left instanceof StringIntegerExpression
          || left instanceof StringCompoundExpression
          || right instanceof StringBooleanExpression
          || right instanceof StringIntegerExpression
          || right instanceof StringCompoundExpression) {
        return newOperator;
      }
      if (left instanceof Variable<?> || left instanceof Constant<?>) {
        if (left.getType() instanceof BuiltinTypes.StringType) {
          return newOperator;
        }
      }
      if (right instanceof Variable<?> || right instanceof Constant<?>) {
        if (right.getType() instanceof BuiltinTypes.StringType) {
          return newOperator;
        }
      }
      if (right instanceof Negation
          && ((Negation) right).getNegated() instanceof StringBooleanExpression) {
        return newOperator;
      }

      if (left instanceof Negation
          && ((Negation) left).getNegated() instanceof StringBooleanExpression) {
        return newOperator;
      }
      if (left instanceof Variable<?> || left instanceof Constant<?>) {
        if (left.getType() instanceof BuiltinTypes.BoolType) {
          return LogicalOperator.EQUIV;
        }
      }
      if (right instanceof Variable<?> || right instanceof Constant<?>) {
        if (right.getType() instanceof BuiltinTypes.BoolType) {
          return LogicalOperator.EQUIV;
        }
      }
      if (right instanceof Negation
          && ((Negation) right).getNegated() instanceof PropositionalCompound) {
        return LogicalOperator.EQUIV;
      }

      if (left instanceof Negation
          && ((Negation) left).getNegated() instanceof PropositionalCompound) {
        return LogicalOperator.EQUIV;
      }
    }

    if (operator.equals(NumericComparator.NE)) {
      Expression left = tmp.poll();
      Expression right = tmp.poll();
      if (left instanceof PropositionalCompound || right instanceof PropositionalCompound) {
        return LogicalOperator.XOR;
      }
      if (left instanceof Variable<?> || left instanceof Constant<?>) {
        if (left.getType() instanceof BuiltinTypes.BoolType) {
          return LogicalOperator.XOR;
        }
      }
      if (right instanceof Variable<?> || right instanceof Constant<?>) {
        if (right.getType() instanceof BuiltinTypes.BoolType) {
          return LogicalOperator.XOR;
        }
      }
      if (right instanceof Negation
          && ((Negation) right).getNegated() instanceof PropositionalCompound) {
        return LogicalOperator.XOR;
      }

      if (left instanceof Negation
          && ((Negation) left).getNegated() instanceof PropositionalCompound) {
        return LogicalOperator.XOR;
      }
    }
    return operator;
  }

  private boolean checkImpliesOperatorRequirements(
      final ExpressionOperator operator, final Queue<Expression> arguments)
      throws SMTLIBParserExceptionInvalidMethodCall {
    if (operator.equals(LogicalOperator.IMPLY)) {
      if (arguments.size() == 2) {
        return true;
      } else {
        throw new SMTLIBParserExceptionInvalidMethodCall(
            "Implies can only work with exactly two arguments, but got: " + arguments);
      }
    }
    return false;
  }

  private static class Tuple<L, R> {
    protected L left;
    protected R right;

    private Tuple(final L left, final R right) {
      this.left = left;
      this.right = right;
    }
  }
}
