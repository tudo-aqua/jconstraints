package structuralEquivalence.expressionVisitor;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import org.junit.Test;
import structuralEquivalence.Processor;

import java.io.File;
import java.util.HashMap;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class OperatorStatisticsTestQFLIATest {

	@Test
	public void parsing100_correcstr_readable_smt2Test(){
		SMTProblem problem = Processor.parseFile(new File(this.getClass()
															  .getClassLoader()
															  .getResource("QF_LIA/prp-0-14.smt2")
															  .getFile()));
		OperatorStatistics visitor = new OperatorStatistics();
		HashMap<String, Integer> data = new HashMap<>();
		problem.getAllAssertionsAsConjunction().accept(visitor, data);
		assertFalse(data.isEmpty());
		assertTrue(data.containsKey("let"));
		assertTrue(data.containsKey("ite"));
		assertTrue(data.containsKey("<="));
		assertTrue(data.containsKey("+"));
		assertTrue(data.containsKey("=="));
	}

}
