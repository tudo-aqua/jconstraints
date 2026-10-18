package gov.nasa.jpf.constraints.expressions;

import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.math.BigInteger;
import java.util.Properties;
import java.util.function.Function;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Comparisons of bitvectors computed from integers are translated to integer arithmetic: the results must agree
 * with Java semantics (wrap-around), for values inside and outside of the range of the bitvector.
 */
public class BitvectorLiftingTest {

  private static final long[] VALUES = {0, 1, 44, 127, 128, 255, 256, 32767, 32768, 65535, 65536, 65580,
      Integer.MAX_VALUE, 1L + Integer.MAX_VALUE, (1L << 32) + 5, -1, -129, -65536, Integer.MIN_VALUE,
      Integer.MIN_VALUE - 1L};

  private ConstraintSolver solver;
  private final Variable<BigInteger> x = Variable.create(BuiltinTypes.INTEGER, "x");

  @BeforeEach
  public void initialize() {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    solver = ConstraintSolverFactory.createSolver("z3", conf);
  }

  private void check(String name, Expression<Boolean> e, java.util.function.LongPredicate expected) {
    for (long v : VALUES) {
      Expression<Boolean> fix = NumericBooleanExpression.create(x, NumericComparator.EQ,
          Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(v)));
      ConstraintSolver.Result r = solver.solve(ExpressionUtil.and(fix, e), new Valuation());
      assertEquals(expected.test(v) ? ConstraintSolver.Result.SAT : ConstraintSolver.Result.UNSAT, r,
          name + " for x = " + v);
    }
  }

  private Expression<Integer> asInt() {
    return CastExpression.create(x, BuiltinTypes.SINT32);
  }

  private Expression<Integer> i(int v) {
    return Constant.create(BuiltinTypes.SINT32, v);
  }

  @Test
  public void intComparisons() {
    check("(int) x < 0", NumericBooleanExpression.create(asInt(), NumericComparator.LT, i(0)),
        v -> (int) v < 0);
    check("(int) x bvsgt 44", BitvectorBooleanExpression.create(asInt(), BitvectorComparator.SGT, i(44)),
        v -> (int) v > 44);
    check("(int) x bvult 44", BitvectorBooleanExpression.create(asInt(), BitvectorComparator.ULT, i(44)),
        v -> Integer.compareUnsigned((int) v, 44) < 0);
    check("(int) x == -1", NumericBooleanExpression.create(asInt(), NumericComparator.EQ, i(-1)),
        v -> (int) v == -1);
  }

  @Test
  public void arithmeticWrapsAround() {
    check("(int) x + MAX < 0", NumericBooleanExpression.create(
            NumericCompound.create(asInt(), NumericOperator.PLUS, i(Integer.MAX_VALUE)), NumericComparator.LT, i(0)),
        v -> (int) v + Integer.MAX_VALUE < 0);
    check("(int) x bvsub 3 bvsge 0", BitvectorBooleanExpression.create(
            BitvectorExpression.create(asInt(), BitvectorOperator.SUB, i(3)), BitvectorComparator.SGE, i(0)),
        v -> (int) v - 3 >= 0);
    check("(int) x * 65536 < 0", NumericBooleanExpression.create(
            NumericCompound.create(asInt(), NumericOperator.MUL, i(65536)), NumericComparator.LT, i(0)),
        v -> (int) v * 65536 < 0);
  }

  @Test
  public void charsAndExtensions() {
    // the char pattern of SPouT: zero_extend 16 ((sint16) x)
    Expression<?> c = BitVectorFunction.zeroExtend(16, CastExpression.create(x, BuiltinTypes.SINT16));
    check("zext((short) x) bvslt 44", BitvectorBooleanExpression.create(c, BitvectorComparator.SLT, i(44)),
        v -> ((short) v & 0xFFFF) < 44);
    Expression<?> s = BitVectorFunction.signExtend(16, CastExpression.create(x, BuiltinTypes.SINT16));
    check("sext((short) x) bvslt 0", BitvectorBooleanExpression.create(s, BitvectorComparator.SLT, i(0)),
        v -> (short) v < 0);
    check("(int) (char) x > 65500", NumericBooleanExpression.create(
            CastExpression.create(CastExpression.create(x, BuiltinTypes.UINT16), BuiltinTypes.SINT32),
            NumericComparator.GT, i(65500)),
        v -> (int) (char) v > 65500);
    check("(int) (byte) x < 0", NumericBooleanExpression.create(
            CastExpression.create(CastExpression.create(x, BuiltinTypes.SINT8), BuiltinTypes.SINT32),
            NumericComparator.LT, i(0)),
        v -> (int) (byte) v < 0);
    check("extract 15..8 ((int) x) == 1", BitvectorBooleanExpression.create(
            BitVectorFunction.extract(15, 8, asInt()), BitvectorComparator.EQ,
            Constant.create(BuiltinTypes.SINT8, (byte) 1)),
        v -> ((v >> 8) & 0xFF) == 1);
  }

  @Test
  public void iteAndCastBack() {
    Expression<Integer> ite = IfThenElse.create(
        NumericBooleanExpression.create(asInt(), NumericComparator.EQ, i(44)), i(0), i(-1));
    check("ite((int) x == 44, 0, -1) bvsge 0", BitvectorBooleanExpression.create(ite, BitvectorComparator.SGE, i(0)),
        v -> (int) v == 44);
    Function<Long, Long> back = v -> (long) (int) (long) v;
    for (long w : new long[] {-1, 5, Integer.MIN_VALUE}) {
      check("(Int) (int) x == " + w, NumericBooleanExpression.create(
              CastExpression.create(asInt(), BuiltinTypes.INTEGER), NumericComparator.EQ,
              Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(w))),
          v -> back.apply(v) == w);
    }
  }

  @Test
  public void stringLengthAndCharacters() {
    // the decisions of StringTokenizer: decided quickly in the integer domain
    Variable<String> str = Variable.create(BuiltinTypes.STRING, "str");
    Expression<Integer> len = CastExpression.create(StringIntegerExpression.createLength(str), BuiltinTypes.SINT32);
    Expression<?> c1 = BitVectorFunction.zeroExtend(16, CastExpression.create(
        StringIntegerExpression.createToCodePoint(StringCompoundExpression.createAt(str,
            Constant.create(BuiltinTypes.INTEGER, BigInteger.ONE))), BuiltinTypes.SINT16));
    Expression<?> c0 = BitVectorFunction.zeroExtend(16, CastExpression.create(
        StringIntegerExpression.createToCodePoint(StringCompoundExpression.createAt(str,
            Constant.create(BuiltinTypes.INTEGER, BigInteger.ZERO))), BuiltinTypes.SINT16));
    Valuation val = new Valuation();
    long start = System.currentTimeMillis();
    assertEquals(ConstraintSolver.Result.SAT, solver.solve(ExpressionUtil.and(
        NumericBooleanExpression.create(StringIntegerExpression.createLength(str), NumericComparator.LE,
            Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(Integer.MAX_VALUE))),
        NumericBooleanExpression.create(StringIntegerExpression.createToCodePoint(StringCompoundExpression.createAt(
            str, Constant.create(BuiltinTypes.INTEGER, BigInteger.ONE))), NumericComparator.LE,
            Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(65535))),
        NumericBooleanExpression.create(StringIntegerExpression.createToCodePoint(StringCompoundExpression.createAt(
            str, Constant.create(BuiltinTypes.INTEGER, BigInteger.ZERO))), NumericComparator.LE,
            Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(65535))),
        BitvectorBooleanExpression.create(len, BitvectorComparator.SGT, i(2)),
        BitvectorBooleanExpression.create(c0, BitvectorComparator.EQ, i('a')),
        BitvectorBooleanExpression.create(c1, BitvectorComparator.EQ, i(',')),
        BitvectorBooleanExpression.create(IfThenElse.create(
            BitvectorBooleanExpression.create(c1, BitvectorComparator.EQ, i(44)), i(0), i(-1)),
            BitvectorComparator.SGE, i(0))), val));
    String model = (String) val.getValue(str);
    assertEquals(true, model.length() > 2 && model.startsWith("a,"), "model: " + model);
    long time = System.currentTimeMillis() - start;
    assertEquals(true, time < 5000, "time: " + time);
  }
}
