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

package gov.nasa.jpf.constraints.smtlibUtility.smtconverter;

import static gov.nasa.jpf.constraints.expressions.RegExOperator.LOOP;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.BitVectorFunction;
import gov.nasa.jpf.constraints.expressions.BitVectorFunction.BVFCT;
import gov.nasa.jpf.constraints.expressions.BitvectorBooleanExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorNegation;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.FloatingPointBooleanExpression;
import gov.nasa.jpf.constraints.expressions.FloatingPointFunction;
import gov.nasa.jpf.constraints.expressions.FloatingPointFunction.FPFCT;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
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
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ConversionUtil;
import gov.nasa.jpf.constraints.types.BVIntegerType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.ConcreteFloatingPointType;
import gov.nasa.jpf.constraints.types.Type;
import java.math.BigInteger;

public class SMTLibExportVisitor extends AbstractExpressionVisitor<Void, Void> {
  private final String ROUNDING_MODE = "RNE";
  private final String TO_FLOAT_32 = "(_ to_fp 8 24)";
  private final String TO_FLOAT_64 = "(_ to_fp 11 53)";
  private final SMTLibExportGenContext ctx;
  private SMTLibExportVisitorConfig config;

  public SMTLibExportVisitor(SMTLibExportGenContext ctx, SMTLibExportVisitorConfig config) {
    this.ctx = ctx;
    this.config = config;
  }

  public SMTLibExportVisitor(SMTLibExportGenContext ctx) {
    this(ctx, new SMTLibExportVisitorConfig());
  }

  public String transform(Expression<?> e) {
    ctx.open("assert");
    if (config.namedAssert) {
      ctx.open("!");
    }
    defaultVisit(e, null);
    String name = null;
    if (config.namedAssert) {
      name = String.format("__stmt%d__", ++config.stmtCounter);
      ctx.append(String.format(":named %s", name));
      ctx.close();
    }
    ctx.close();
    ctx.flush();
    return name;
  }

  @Override
  public <E> Void visit(Variable<E> var, Void v) {
    ctx.appendVar(var);
    return null;
  }

  @Override
  public <E> Void visit(Constant<E> c, Void v) {
    // TODO: add missing data types
    if (BuiltinTypes.SINT32.equals(c.getType())) {
      Integer i = (Integer) c.getValue();
      ctx.append("#x" + String.format("%1$08x", i));
    } else if (BuiltinTypes.SINT64.equals(c.getType())) {
      Long l = (Long) c.getValue();
      ctx.append("#x" + String.format("%1$016x", l));
    } else if (BuiltinTypes.SINT8.equals(c.getType())) {
      Byte i = (Byte) c.getValue();
      ctx.append("#x" + String.format("%1$02x", i));
    } else if (BuiltinTypes.UINT16.equals(c.getType())) {
      char i = (Character) c.getValue();
      ctx.append("#x" + String.format("%1$04x", (int) i));
    } else if (BuiltinTypes.INTEGER.equals(c.getType())) {
      BigInteger i = (BigInteger) c.getValue();
      if (i.compareTo(BigInteger.ZERO) < 0) {
        ctx.open("-");
        ctx.append(i.toString().replace("-", ""));
        ctx.close();
      } else {
        ctx.append(i.toString());
      }
    } else if (BuiltinTypes.STRING.equals(c.getType())) {
      String s = (String) c.getValue();
      if (config.replaceZ3Escape) {
        s = ConversionUtil.convertZ3EncodingToSMTLib(s);
      }
      s = s.replaceAll("\"", "\"\"");
      ctx.append("\"" + s + "\"");
    } else if (BuiltinTypes.BOOL.equals(c.getType())) {
      ctx.append(c.getValue().toString());
    } else if (BuiltinTypes.DOUBLE.equals(c.getType())) {
      convertDouble((Constant<Double>) c);
    } else if (BuiltinTypes.FLOAT.equals(c.getType())) {
      convertFloat((Constant<Float>) c);
    } else {
      throw new IllegalArgumentException("Unsupported const type: " + c.getType());
    }
    return null;
  }

  private void convertFloat(Constant<Float> c) {
    float val = (Float) c.getValue();
    String bitValues =
        String.format("%32s", Integer.toBinaryString(Float.floatToRawIntBits(val)))
            .replace(" ", "0");

    String sign = bitValues.substring(0, 1); // 1 Bit sign
    String exponent = bitValues.substring(1, 9); // 11 Bits expnonent
    String mantissa = bitValues.substring(9); // 53 Bits mantissa
    ctx.append(String.format("(fp #b%s #b%s #b%s)", sign, exponent, mantissa));
  }

  private void convertDouble(Constant<Double> c) {
    double val = (Double) c.getValue();
    String bitValues =
        String.format("%64s", Long.toBinaryString(Double.doubleToRawLongBits(val)))
            .replace(" ", "0");

    String sign = bitValues.substring(0, 1); // 1 Bit sign
    String exponent = bitValues.substring(1, 12); // 11 Bits expnonent
    String mantissa = bitValues.substring(12); // 53 Bits mantissa
    ctx.append(String.format("(fp #b%s #b%s #b%s)", sign, exponent, mantissa));
  }

  @Override
  public Void visit(Negation n, Void v) {
    ctx.open("not");
    visit(n.getNegated(), v);
    ctx.close();
    return null;
  }

  @Override
  public Void visit(NumericBooleanExpression n, Void v) {
    ctx.open(numComp(n.getComparator(), n.getLeft().getType()));
    visit(n.getLeft(), v);
    visit(n.getRight(), v);
    ctx.close();
    return null;
  }

  private String numComp(NumericComparator nc, Type<?> t) {
    if (t instanceof ConcreteFloatingPointType) {
      return numCompFP(nc);
    }
    switch (nc) {
      case EQ:
        return "=";
      case NE:
        return "distinct";
      case GE:
        return bvType(t) ? (isSigned(t) ? "bvsge" : "bvuge") : ">=";
      case LE:
        return bvType(t) ? (isSigned(t) ? "bvsle" : "bvule") : "<=";
      case GT:
        return bvType(t) ? (isSigned(t) ? "bvsgt" : "bvugt") : ">";
      case LT:
        return bvType(t) ? (isSigned(t) ? "bvslt" : "bvult") : "<";
      default:
        throw new IllegalArgumentException("Unsupported: " + nc);
    }
  }

  private String numCompFP(NumericComparator nc) {
    switch (nc) {
      case EQ:
        return "fp.eq";
      case NE:
        return "distinct";
      case GE:
        return "fp.ge";
      case GT:
        return "fp.gt";
      case LE:
        return "fp.le";
      case LT:
        return "fp.lt";
      default:
        throw new UnsupportedOperationException(
            "Don't know this numeric comparater in the FP theory: " + nc);
    }
  }

  private boolean bvType(Type<?> t) {
    return BuiltinTypes.SINT8.equals(t)
        || BuiltinTypes.SINT16.equals(t)
        || BuiltinTypes.SINT32.equals(t)
        || BuiltinTypes.SINT64.equals(t)
        || BuiltinTypes.UINT16.equals(t);
  }

  @Override
  public Void visit(RegExBooleanExpression n, Void v) {
    String operator = config.isZ3Mode ? "str.in.re" : "str.in_re";
    ctx.open(operator);
    visit(n.getLeft(), v);
    visit(n.getRight(), v);
    ctx.close();
    return null;
  }

  @Override
  public Void visit(StringBooleanExpression n, Void v) {
    ctx.open(stringComp(n.getOperator()));
    if (n.getOperator().equals(StringBooleanOperator.PREFIXOF)
        || n.getOperator().equals(StringBooleanOperator.SUFFIXOF)) {
      visit(n.getRight(), v);
      visit(n.getLeft(), v);
    } else {
      visit(n.getLeft(), v);
      visit(n.getRight(), v);
    }
    ctx.close();
    return null;
  }

  private String stringComp(StringBooleanOperator op) {
    switch (op) {
      case EQUALS:
        return "=";
      case CONTAINS:
        return "str.contains";
      case PREFIXOF:
        return "str.prefixof";
      case SUFFIXOF:
        return "str.suffixof";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  @Override
  public Void visit(StringIntegerExpression n, Void v) {
    ctx.open(stringIntOp(n.getOperator()));
    visit(n.getLeft(), v);
    if (StringIntegerOperator.INDEXOF.equals(n.getOperator())) {
      visit(n.getRight(), v);
      if (n.getOffset() != null) {
        visit(n.getOffset(), v);
      }
    }
    ctx.close();
    return null;
  }

  private String stringIntOp(StringIntegerOperator op) {
    switch (op) {
      case INDEXOF:
        return "str.indexof";
      case LENGTH:
        return "str.len";
      case TOINT:
        // In QF_S this is str.to_int
        return config.isZ3Mode ? "str.to.int" : "str.to_int";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  @Override
  public Void visit(StringCompoundExpression stringCompoundExpression, Void data) {
    ctx.open(stringCompoundOp(stringCompoundExpression.getOperator()));

    for (Expression child : stringCompoundExpression.getChildren()) {
      visit(child, data);
    }
    ctx.close();
    return null;
  }

  private String stringCompoundOp(StringOperator op) {
    switch (op) {
      case CONCAT:
        return "str.++";
      case SUBSTR:
        return "str.substr";
      case AT:
        return "str.at";
      case TOSTR:
        // In QF_S this is str.from_int
        return config.isZ3Mode ? "int.to.str" : "str.from_int";
      case REPLACE:
        return "str.replace";
      case REPLACEALL:
        return "str.replace_all";
      case TOLOWERCASE:
        return "str.tolower";
      case TOUPPERCASE:
        return "str.toupper";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  @Override
  public Void visit(RegexCompoundExpression n, Void data) {
    ctx.open(regexCompoundOp(n.getOperator()));
    for (Expression child : n.getChildren()) {
      visit(child, data);
    }
    ctx.close();
    return null;
  }

  private String regexCompoundOp(RegExCompoundOperator op) {
    switch (op) {
      case INTERSECTION:
        return "re.inter";
      case UNION:
        return "re.union";
      case CONCAT:
        return "re.++";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  private String regexOp(RegExOperator op) {
    switch (op) {
      case KLEENESTAR:
        return "re.*";
      case KLEENEPLUS:
        return "re.+";
      case LOOP:
        return "re.loop";
      case RANGE:
        return "re.range";
      case OPTIONAL:
        return "re.opt";
      case STRTORE:
        return config.isZ3Mode ? "str.to.re" : "str.to_re";
      case ALLCHAR:
        return "re.allchar";
      case ALL:
        return "re.all";
      case COMPLEMENT:
        return "re.comp";
      case NOSTR:
        return "re.none";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  @Override
  public Void visit(RegexOperatorExpression n, Void data) {
    String operator = regexOp(n.getOperator());
    if (n.getOperator().equals(RegExOperator.ALLCHAR)
        || n.getOperator().equals(RegExOperator.NOSTR)) {
      ctx.append(operator);
    } else if (n.getOperator().equals(LOOP)) {
      ctx.open(String.format("(_ re.loop %s %s)", n.getLow(), n.getHigh()));
      visit(n.getLeft(), data);
      ctx.close();
    } else {
      ctx.open(operator);
      switch (n.getOperator()) {
        case KLEENESTAR:
          visit(n.getLeft(), data);
          break;
        case KLEENEPLUS:
          visit(n.getLeft(), data);
          break;
        case RANGE:
          ctx.append("\"" + n.getCh1() + "\"");
          ctx.append("\"" + n.getCh2() + "\"");
          break;
        case OPTIONAL:
          visit(n.getLeft(), data);
          break;
        case STRTORE:
          String value = n.getS();
          if (value != null) {
            ctx.append("\"" + value + "\"");
          } else {
            visit(n.getLeft(), data);
          }
          break;
        case ALLCHAR:
          break;
        case ALL:
          throw new UnsupportedOperationException();
        case COMPLEMENT:
          visit(n.getLeft(), data);
          break;
        case NOSTR:
          break;
        default:
          throw new UnsupportedOperationException();
      }
      ctx.close();
    }
    return null;
  }

  @Override
  public <F, E> Void visit(CastExpression<F, E> cast, Void v) {
    if (BuiltinTypes.INTEGER.equals(cast.getCasted().getType())
        && BuiltinTypes.SINT32.equals(cast.getType())) {
      return castIntegerSINTX(cast, 32);
    } else if (BuiltinTypes.INTEGER.equals(cast.getCasted().getType())
        && BuiltinTypes.SINT8.equals(cast.getType())) {
      return castIntegerSINTX(cast, 8);
    } else if (BuiltinTypes.SINT32.equals(cast.getCasted().getType())
        && BuiltinTypes.INTEGER.equals(cast.getType())) {
      return castSINTXInteger(cast);
    } else if (BuiltinTypes.SINT8.equals(cast.getCasted().getType())
        && BuiltinTypes.SINT32.equals(cast.getType())) {
      return castSignExtend(cast.getCasted(), 24);
    } else if (BuiltinTypes.SINT8.equals(cast.getCasted().getType())
        && BuiltinTypes.UINT16.equals(cast.getType())) {
      // This is a byte to char cast in the jConstraints semantic:
      // https://docs.oracle.com/javase/specs/jls/se8/html/jls-5.html#jls-5.1.4
      return castSignExtend(cast.getCasted(), 8);
    } else if (BuiltinTypes.UINT16.equals(cast.getCasted().getType())
        && BuiltinTypes.SINT32.equals(cast.getType())) {
      // This is a char to byte cast in the jConstraints semantic:
      // https://docs.oracle.com/javase/specs/jls/se8/html/jls-5.html#jls-5.1.2
      return castZeroExtend(cast.getCasted(), 16);
    } else if (BuiltinTypes.SINT32.equals(cast.getCasted().getType())
        && BuiltinTypes.UINT16.equals(cast.getType())) {
      // we extract bits with index 0 - 15 from the array.
      return castExtract(cast, 15);
    } else if (BuiltinTypes.FLOAT.equals(cast.getType())
        && (BuiltinTypes.SINT32.equals(cast.getCasted().getType())
            || BuiltinTypes.SINT64.equals(cast.getCasted().getType())
            || BuiltinTypes.DOUBLE.equals(cast.getCasted().getType()))) {
      return castFP2F((Expression<Integer>) cast.getCasted());
    } else if (BuiltinTypes.SINT32.equals(cast.getType())
        && (BuiltinTypes.FLOAT.equals(cast.getCasted().getType())
            || BuiltinTypes.DOUBLE.equals(cast.getCasted().getType()))) {
      return castFP2Int((Expression<Float>) cast.getCasted());
    } else if (BuiltinTypes.DOUBLE.equals(cast.getType())
        && (BuiltinTypes.SINT32.equals(cast.getCasted().getType())
            || BuiltinTypes.SINT64.equals(cast.getCasted().getType())
            || BuiltinTypes.FLOAT.equals(cast.getCasted().getType()))) {
      return castFP2D((Expression<Integer>) cast.getCasted());
    } else if (BuiltinTypes.SINT64.equals(cast.getType())
        && (BuiltinTypes.DOUBLE.equals(cast.getCasted().getType())
            || BuiltinTypes.FLOAT.equals(cast.getCasted().getType()))) {
      return castFP2Long(cast.getCasted());
    } else {
      throw new UnsupportedOperationException(
          String.format(
              "casting is not supported by SMTLib support currently. Cannot Cast: %s to: %s",
              cast.getCasted().getType(), cast.getType()));
    }
  }

  @Override
  public <E> Void visit(NumericCompound<E> n, Void v) {
    ctx.open(numOp(n.getOperator(), n.getType()));
    visit(n.getLeft(), v);
    visit(n.getRight(), v);
    ctx.close();
    return null;
  }

  private String numOp(NumericOperator op, Type t) {
    if (t instanceof ConcreteFloatingPointType) {
      return resolveFPnumericalOp(op);
    }
    switch (op) {
      case DIV:
        return bvType(t)
            ? (isSigned(t) ? "bvsdiv" : "bvudiv")
            : (BuiltinTypes.REAL.equals(t) ? "/" : "div");
      case MINUS:
        return bvType(t) ? "bvsub" : "-";
      case MUL:
        return bvType(t) ? "bvmul" : "*";
      case PLUS:
        return bvType(t) ? "bvadd" : "+";
      case REM:
        return bvType(t) ? (isSigned(t) ? "bvsrem" : "bvurem") : "mod";
      case MOD:
        return bvType(t) ? (isSigned(t) ? "bvsmod" : "bvurem") : "mod";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  private String resolveFPnumericalOp(NumericOperator op) {
    switch (op) {
      case MUL:
        return "fp.mul " + ROUNDING_MODE;
      case DIV:
        return "fp.div " + ROUNDING_MODE;
      case MOD:
        throw new UnsupportedOperationException("FP theory only supports remainder, no modulo");
      case REM:
        return "fp.rem";
      case PLUS:
        return "fp.add " + ROUNDING_MODE;
      case MINUS:
        return "fp.sub " + ROUNDING_MODE;
      default:
        throw new UnsupportedOperationException(
            "Don't know this numeirc operator with FP theory: " + op);
    }
  }

  private boolean isSigned(Type t) {
    if (t instanceof BVIntegerType) {
      BVIntegerType casted = (BVIntegerType) t;
      return casted.isSigned();
    }
    throw new IllegalArgumentException("The type must be a BV type");
  }

  @Override
  public Void visit(PropositionalCompound n, Void v) {
    ctx.open(logicOp(n.getOperator()));
    visit(n.getLeft(), v);
    visit(n.getRight(), v);
    ctx.close();
    return null;
  }

  private String logicOp(LogicalOperator op) {
    switch (op) {
      case AND:
        return "and";
      case IMPLY:
        return "=>";
      case OR:
        return "or";
      case EQUIV:
        return "=";
      case XOR:
        return "xor";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  @Override
  public <E> Void visit(IfThenElse<E> n, Void v) {
    ctx.open("ite");
    visit(n.getIf(), v);
    visit(n.getThen(), v);
    visit(n.getElse(), v);
    ctx.close();
    return null;
  }

  @Override
  public <E> Void visit(UnaryMinus<E> n, Void v) {
    if (n.getNegated().getType() instanceof BVIntegerType) {
      ctx.open("bvneg");
    } else if (n.getNegated().getType() instanceof ConcreteFloatingPointType) {
      ctx.open("fp.neg");
    } else {
      ctx.open("-");
    }
    visit(n.getNegated(), v);
    ctx.close();
    return null;
  }

  @Override
  public <E> Void visit(BitvectorExpression<E> n, Void v) {
    ctx.open(bvOp((n.getOperator())));
    visit(n.getLeft(), v);
    visit(n.getRight(), v);
    ctx.close();
    return null;
  }

  @Override
  public Void visit(BitvectorBooleanExpression n, Void v) {
    ctx.open(n.getComparator().toString());
    visit(n.getLeft(), v);
    visit(n.getRight(), v);
    ctx.close();
    return null;
  }

  @Override
  public <F, E> Void visit(BitVectorFunction<F, E> n, Void v) {
    BVFCT operator = n.getFunction();
    int[] params = n.getParams();
    switch (operator) {
      case EXTRACT:
        assert params.length == 2;
        castExtract(n.getArgument(), params[0], params[1]);
      case SIGN_EXTEND:
        assert params.length == 1;
        castSignExtend(n.getArgument(), params[0]);
      case ZERO_EXTEND:
        castZeroExtend(n.getArgument(), params[0]);
      default:
        throw new UnsupportedOperationException(
            "SMTLib export is not implemented for : " + operator);
    }
  }

  @Override
  public <F, E> Void visit(FloatingPointFunction<F, E> n, Void v) {
    FPFCT operator = n.getFunction();
    switch (operator) {
      case FP_ADD:
        ctx.open("fp.add " + n.getRmode());
        break;
      case FP_DIV:
        ctx.open("fp.div " + n.getRmode());
        break;
      case FP_MUL:
        ctx.open("fp.mul " + n.getRmode());
        break;
      case FP_SUB:
        ctx.open("fp.sub " + n.getRmode());
        break;
      case FP_REM:
        ctx.open("fp.rem");
        break;
      case FP_NEG:
        ctx.open("fp.neg");
        assert n.getChildren().length == 1;
        visit(n.getChildren()[0], v);
        ctx.close();
        return null;
      case TO_FP:
        assert n.getChildren().length == 1;
        if (n.getType().equals(BuiltinTypes.DOUBLE)) {
          castFP2D(n.getChildren()[0]);
        } else if (n.getType().equals(BuiltinTypes.FLOAT)) {
          castFP2F(n.getChildren()[0]);
        } else {
          throw new UnsupportedOperationException(
              "Cannot cast FP Function with type: " + n.getType());
        }
        return null;
      case FP_TO_SBV:
        assert n.getChildren().length == 1;
        if (n.getType().equals(BuiltinTypes.SINT32)) {
          castFP2Int(n.getChildren()[0]);
        } else if (n.getType().equals(BuiltinTypes.SINT64)) {
          castFP2Long(n.getChildren()[0]);
        } else {
          throw new UnsupportedOperationException("Cannot cast FP to BV with type: " + n.getType());
        }
        return null;
      default:
        throw new UnsupportedOperationException(
            "Cannot convert FloatingPointFunction with operator: " + operator);
    }
    for (Expression e : n.getChildren()) {
      visit(e, v);
    }
    ctx.close();
    return null;
  }

  @Override
  public <E> Void visit(FloatingPointBooleanExpression<E> n, Void v) {
    ctx.open(n.getOperator().toString());
    for (Expression e : n.getChildren()) {
      visit(e, v);
    }
    ctx.close();
    return null;
  }

  private String bvOp(BitvectorOperator op) {
    switch (op) {
      case AND:
        return "bvand";
      case OR:
        return "bvor";
      case XOR:
        return "bvxor";
      case SHIFTL:
        return "bvshl";
      case SHIFTR:
        return "bvashr";
      case SHIFTUR:
        return "bvlshr";
      case MUL:
        return "bvmul";
      case UREM:
        return "bvurem";
      case SREM:
        return "bvsrem";
      case SDIV:
        return "bvsdiv";
      case ADD:
        return "bvadd";
      case SUB:
        return "bvsub";
      case UDIV:
        return "bvudiv";

      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  @Override
  public <E> Void visit(BitvectorNegation<E> n, Void v) {
    ctx.open("bvnot");
    visit(n.getNegated(), v);
    ctx.close();
    return null;
  }

  @Override
  public Void visit(QuantifierExpression q, Void v) {
    // TODO: this is untested!
    ctx.open("" + q.getQuantifier());
    ctx.open("");
    for (Variable<?> var : q.getBoundVariables()) {
      ctx.appendLocalVarDecl(var);
    }
    ctx.close();
    visit(q.getBody());
    ctx.close();
    return null;
  }

  @Override
  public <E> Void visit(FunctionExpression<E> f, Void data) {
    throw new UnsupportedOperationException("not implemented yet.");
    // TODO: implement support for function expressions
    // return null;
  }

  @Override
  public Void visit(LetExpression n, Void v) {
    ctx.open("let");
    ctx.open("");
    for (Variable<?> var : n.getParameters()) {
      ctx.registerLocalSymbol(var);
      ctx.open(var.getName());
      // FIXME: can this be null?
      visit(n.getParameterValues().get(var), v);
      ctx.close();
    }
    ctx.close();
    visit(n.getMainValue(), v);
    ctx.close();
    return null;
  }

  @Override
  protected <E> Void defaultVisit(Expression<E> expression, Void v) {
    visit(expression, v);
    return null;
  }

  /* Below this line should only be private casting methods
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*/
  private Void castIntegerSINTX(CastExpression cast, int bits) {
    ctx.open(String.format("(_ int2bv %d)", bits));
    visit(cast.getCasted());
    ctx.close();
    return null;
  }

  private Void castSINTXInteger(CastExpression cast) {
    ctx.open("ite");
    ctx.open("bvslt");
    visit(cast.getCasted());
    visit(Constant.create(BuiltinTypes.SINT32, 0));
    ctx.close();
    ctx.open("-");
    ctx.open("bv2nat");
    visit(cast.getCasted());
    ctx.close();
    ctx.close();
    ctx.open("bv2nat");
    visit(cast.getCasted());
    ctx.close();
    ctx.close();
    return null;
  }

  private Void castSignExtend(Expression cast, int bits) {
    ctx.open(String.format("(_ sign_extend %d)", bits));
    visit(cast);
    ctx.close();
    return null;
  }

  private Void castZeroExtend(Expression cast, int bits) {
    ctx.open(String.format("(_ zero_extend %d)", bits));
    visit(cast);
    ctx.close();
    return null;
  }

  private <F> Void castFP2D(Expression<F> casted) {
    ctx.open(TO_FLOAT_64 + " " + ROUNDING_MODE);
    visit(casted);
    ctx.close();
    return null;
  }

  private <E> Void castFP2F(Expression<E> casted) {
    ctx.open(TO_FLOAT_32 + " " + ROUNDING_MODE);
    visit(casted);
    ctx.close();
    return null;
  }

  private <E> Void castFP2Int(Expression<E> casted) {
    ctx.open("(_ fp.to_sbv 32) " + ROUNDING_MODE);
    visit(casted);
    ctx.close();
    return null;
  }

  private <F> Void castFP2Long(Expression<F> casted) {
    ctx.open("(_ fp.to_sbv 64) " + ROUNDING_MODE);
    visit(casted);
    ctx.close();
    return null;
  }

  private Void castExtract(Expression cast, int highBits, int lowBits) {
    ctx.open(String.format("(_ extract %d %d)", highBits, lowBits));
    visit(cast);
    ctx.close();
    return null;
  }

  private Void castExtract(CastExpression cast, int bits) {
    return castExtract(cast.getCasted(), bits, 0);
  }
}
