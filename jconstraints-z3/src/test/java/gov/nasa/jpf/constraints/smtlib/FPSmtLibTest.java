package gov.nasa.jpf.constraints.smtlib;

import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import java.io.IOException;
import org.junit.jupiter.api.Test;

public class FPSmtLibTest {

  @Test
  public void solvingFPFunc_Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun f0 () (_ FloatingPoint 8 24)) (assert (fp.eq f0 f0))");

    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.println(expr.toString());
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    System.out.println(model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
  }

  @Test
  public void solvingFPFuncCast_Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun b0 () (_ BitVec 32)) (declare-fun f0 () (_ FloatingPoint 11 53)) (assert (= b0 ((_ fp.to_sbv 32) (RNE RoundingMode) ((_ to_fp 8 24) (RNE RoundingMode) (fp.add (RNE RoundingMode) f0 f0)))))");

    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.println(expr.toString());
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    System.out.println(model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
  }
}
