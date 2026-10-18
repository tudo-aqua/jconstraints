package gov.nasa.jpf.constraints.expressions;

import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.Properties;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/** toLowerCase / toUpperCase (character-wise, exact for ASCII) and the decoding of string models */
public class StringCaseTest {

  private ConstraintSolver solver;

  @BeforeEach
  public void initialize() {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    solver = ConstraintSolverFactory.createSolver("z3", conf);
  }

  private Valuation solve(ConstraintSolver.Result expected, Expression<Boolean>... constraints) {
    Valuation val = new Valuation();
    assertEquals(expected, solver.solve(ExpressionUtil.and(constraints), val));
    return val;
  }

  @Test
  public void toLowerIsExactForAscii() {
    Variable<String> s = Variable.create(BuiltinTypes.STRING, "s");
    Valuation val = solve(ConstraintSolver.Result.SAT,
        StringBooleanExpression.createEquals(StringCompoundExpression.createToLower(s), Constant.create(BuiltinTypes.STRING, "abc")),
        new Negation(StringBooleanExpression.createEquals(s, Constant.create(BuiltinTypes.STRING, "abc"))));
    String model = (String) val.getValue(s);
    assertEquals("abc", model.toLowerCase());
  }

  @Test
  public void toUpperOfLowerCaseLetter() {
    Variable<String> s = Variable.create(BuiltinTypes.STRING, "s");
    // "a".toUpperCase() is "A": the negation is unsatisfiable
    solve(ConstraintSolver.Result.UNSAT,
        StringBooleanExpression.createEquals(s, Constant.create(BuiltinTypes.STRING, "a")),
        new Negation(StringBooleanExpression.createEquals(StringCompoundExpression.createToUpper(s),
            Constant.create(BuiltinTypes.STRING, "A"))));
  }

  @Test
  public void modelWithNonAsciiCharacter() {
    Variable<String> s = Variable.create(BuiltinTypes.STRING, "s");
    // a single character with code 0x80 .. 0x2ff: printed as an escape sequence by Z3
    Expression<java.math.BigInteger> code = StringIntegerExpression.createToCodePoint(s);
    Valuation val = solve(ConstraintSolver.Result.SAT,
        NumericBooleanExpression.create(code, NumericComparator.GT,
            Constant.create(BuiltinTypes.INTEGER, java.math.BigInteger.valueOf(0x7f))),
        NumericBooleanExpression.create(code, NumericComparator.LT,
            Constant.create(BuiltinTypes.INTEGER, java.math.BigInteger.valueOf(0x300))));
    String model = (String) val.getValue(s);
    assertEquals(1, model.length(), "model: " + model);
    int c = model.charAt(0);
    assertEquals(true, c > 0x7f && c < 0x300, "model: " + model);
  }

  @Test
  public void fromCodeAndToCode() {
    Variable<java.math.BigInteger> x = Variable.create(BuiltinTypes.INTEGER, "x");
    Valuation val = solve(ConstraintSolver.Result.SAT,
        StringBooleanExpression.createEquals(StringCompoundExpression.createFromCode(x),
            Constant.create(BuiltinTypes.STRING, "B")));
    assertEquals(java.math.BigInteger.valueOf(66), val.getValue(x));
    Variable<String> s = Variable.create(BuiltinTypes.STRING, "s");
    solve(ConstraintSolver.Result.UNSAT,
        StringBooleanExpression.createEquals(s, Constant.create(BuiltinTypes.STRING, "B")),
        new Negation(NumericBooleanExpression.create(StringIntegerExpression.createToCodePoint(s),
            NumericComparator.EQ, Constant.create(BuiltinTypes.INTEGER, java.math.BigInteger.valueOf(66)))));
  }
}
