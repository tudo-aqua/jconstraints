package gov.nasa.jpf.constraints.parser;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import org.testng.annotations.Test;

public class ArrayParserTest {


    @Test(groups = {"parser", "base"})
    public void arrayDeclarationParserTest()
            throws Exception {
        final String input =
                "(declare-fun arr1 () (Array Int Int))\n" +
                "(declare-fun arr2 () (Array Int Int))\n" +
                "(declare-fun x1 () Int)\n" +
                "(assert (= x1 3))\n" +
                "(declare-fun y1 () Int)\n" +
                "(assert (= y1 2))\n" +
                "(assert (= (store arr1 x1 y1) arr1))\n" +
                "(declare-fun x2 () Int)\n" +
                "(assert (= x2 3))\n" +
                "(declare-fun y2 () Int)\n" +
                "(assert (= y2 2))\n" +
                "(assert (= (store arr2 x2 y2) arr2))\n" +
                "(declare-fun z1 () Int)\n" +
                "(assert (= z1 (select arr1 3)))\n" +
                "(declare-fun z2 () Int)\n" +
                "(assert (= z2 (select arr2 3)))\n" +
                "(assert (= z1 z2))\n" +
                "(check-sat)\n" +
                "(get-model)\n";
        SMTLIBParser smtlibParser = new SMTLIBParser();
        final SMTProblem problem = smtlibParser.parseSMTProgram(input);
        System.out.println(problem.toString());


    }
}
