package io.github.tudoaqua.jconstraints.cvc5.smtlibBenchmarks;

import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.SAT;
import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import io.github.tudoaqua.jconstraints.cvc5.AbstractCVC5Test;
import java.io.IOException;
import org.junit.jupiter.api.Test;

public class SMTLibSnippetsParsingTest extends AbstractCVC5Test {

  @Test
  public void testUsedInMulti() throws IOException, SMTLIBParserException {
    String problem =
        "(declare-const __string_0 String)\n"
            + "(assert (not (bvslt (bvsub ((_ int2bv 32) (str.len __string_0)) #x00000001) #x00000000)))\n"
            + "(assert (<= 0 (str.len __string_0)))\n"
            + "(assert (bvslt (bvsub ((_ int2bv 32) (str.len __string_0)) #x00000001) ((_ int2bv 32) (str.len __string_0))))\n"
            + "(declare-const __string_1 String)\n"
            + "(assert (not (bvslt #x00000000 ((_ int2bv 32) (str.len __string_1)))))";

    SMTProblem smtProblem = SMTLIBParser.parseSMTProgram(problem);
    Valuation val = new Valuation();
    Result res1 = cvc5.solve(smtProblem.getAllAssertionsAsConjunction(), val);
    assertEquals(SAT, res1);
    val = new Valuation();
    cvc5Context.add(smtProblem.getAllAssertionsAsConjunction());
    Result res = cvc5Context.solve(val);
    assertEquals(SAT, res);
  }

}
