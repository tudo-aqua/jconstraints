package gov.nasa.jpf.constraints.smtlib;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class UIFTest {
    @Test
    public void Problem1Test() throws IOException, SMTLIBParserException, URISyntaxException {
        URL smtFile = QfLiaTest.class.getClassLoader().getResource("problem_2__008.smt2");
        SMTProblem problem =
                SMTLIBParser.parseSMTProgram(
                        "(declare-fun extends (String String) Bool)" +
                              "(assert (extends \"a\" \"b\"))");


        NativeZ3Solver z3 = new NativeZ3Solver();
        Valuation model = new Valuation();
        ConstraintSolver.Result jRes = z3.solve(problem.getAllAssertionsAsConjunction(), model);
        assertEquals(ConstraintSolver.Result.SAT, jRes);
    }
    @Test
    public void Problem2Test() throws IOException, SMTLIBParserException, URISyntaxException {
        URL smtFile = QfLiaTest.class.getClassLoader().getResource("problem_2__008.smt2");
        SMTProblem problem =
                SMTLIBParser.parseSMTProgram(
                        "(declare-fun extends (String String) Bool)" +
                                "(assert (extends \"a\" \"b\"))" +
                                "(assert (not (extends \"a\" \"b\")))"
                );

        NativeZ3Solver z3 = new NativeZ3Solver();
        Valuation model = new Valuation();
        ConstraintSolver.Result jRes = z3.solve(problem.getAllAssertionsAsConjunction(), model);
        assertEquals(ConstraintSolver.Result.UNSAT, jRes);
    }
}
