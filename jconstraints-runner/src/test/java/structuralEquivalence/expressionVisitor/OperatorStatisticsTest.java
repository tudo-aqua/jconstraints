package structuralEquivalence.expressionVisitor;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import org.junit.Test;
import structuralEquivalence.Processor;

import java.io.File;
import java.util.HashMap;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class OperatorStatisticsTest {


	@Test
	public void parsing100_correcstr_readable_smt2Test(){
		SMTProblem problem = Processor.parseFile(new File(this.getClass()
															  .getClassLoader()
															  .getResource("100.corecstrs.readable.smt2")
															  .getFile()));
		OperatorStatistics visitor = new OperatorStatistics();
		HashMap<String, Integer> data = new HashMap<>();
		problem.getAllAssertionsAsConjunction().accept(visitor, data);
		assertEquals((int) data.get("str.to.re"), 43);
		assertEquals((int) data.get("str.++"), 88);
		assertEquals((int) data.get("=="), 59);
		assertEquals((int) data.get("=") , 180);
	}

	@Test
	public void parsingPyEx1Smt2Test(){
		SMTProblem problem = Processor.parseFile(new File(this.getClass()
															  .getClassLoader()
															  .getResource("pyex1.smt2")
															  .getFile()));
		OperatorStatistics visitor = new OperatorStatistics();
		HashMap<String, Integer> data = new HashMap<>();
		problem.getAllAssertionsAsConjunction().accept(visitor, data);
		System.out.println(data);
		assertEquals((int) data.get("str.contains"), 29);
		assertEquals((int) data.get("str.len"), 2188);
		assertEquals((int) data.get("str.++"), 69);
		assertEquals((int) data.get("str.replace") , 69);
	}
}
