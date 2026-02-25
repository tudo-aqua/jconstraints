package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.Properties;

public class FunctionTest {

    @Test
    public void testFunctionDefinition() throws IOException, SMTLIBParserException {
        SMTProblem problem = SMTLIBParser.parseSMTProgram(
            "(declare-fun __object_0.cls () String)\n" +
                    "\n" +
                    "(assert (or\n" +
                    "  (= __object_0.cls \"LA;\")\n" +
                    "  (= __object_0.cls \"LB;\")\n" +
                    "  (= __object_0.cls \"LC;\")\n" +
                    "))\n" +
                    "\n" +
                    "(declare-fun obj.extends (String String) Bool)\n" +
                    "(assert (forall ((sub String) (sup String))\n" +
                    "  (= (obj.extends sub sup)  \n" +
                    "  (ite (or    \n" +
                    "    (and (= sub \"null\") (= sup \"LA;\"))\n" +
                    "    (and (= sub \"null\") (= sup \"LB;\"))\n" +
                    "    (and (= sub \"null\") (= sup \"LC;\"))\n" +
                    "    (and (= sub \"null\") (= sup \"Ltest/D;\"))\n" +
                    "    (and (= sub \"LA;\")  (= sup \"LA;\"))\n" +
                    "    (and (= sub \"LB;\")  (= sup \"LB;\"))\n" +
                    "    (and (= sub \"LB;\")  (= sup \"LA;\"))\n" +
                    "    (and (= sub \"LC;\")  (= sup \"LC;\"))\n" +
                    "    (and (= sub \"LC;\")  (= sup \"LB;\"))\n" +
                    "    (and (= sub \"LC;\")  (= sup \"LA;\"))\n" +
                    "    (and (= sub \"Ltest/D;\") (= sup \"Ltest/D;\"))    \n" +
                    "  ) true false)\n" +
                    ")))\n" +
                    "\n" +
                    "(assert (not (obj.extends __object_0.cls \"LC;\"))) \n" +
                    "\n" +
                    "(check-sat)\n" +
                    "(get-model)"
        );
        Properties conf = new Properties();
        conf.setProperty("symbolic.dp", "z3");
        ConstraintSolver solver = ConstraintSolverFactory.createSolver("z3", conf);
        Valuation val = new Valuation();
        ConstraintSolver.Result result = solver.solve(problem.getAllAssertionsAsConjunction(), val);
        System.out.println("Result: " + result);
        System.out.println("Valuation: " + val);

    }
}
