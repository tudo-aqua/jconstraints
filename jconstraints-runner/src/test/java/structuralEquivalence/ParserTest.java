package structuralEquivalence;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import org.junit.Test;

import java.io.File;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;


public class ParserTest {

	@Test
	public void parsingTest(){
		SMTProblem problem = Processor.parseFile(new File(
																						 "/Users/maltemues/Development/string_constraints/models/slothtests/sloth/norn-benchmark-9b.smt2"));

		assertTrue(Processor.compareProblems(problem, problem));
	}




}
