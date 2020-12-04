package structuralEquivalence;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import org.junit.Before;
import org.junit.Test;

import java.io.File;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ProcessorTest {

	SMTProblem problem1, problem2, problem3, problem4, p5, p6, p7, p8;


	@Before
	public void setup(){
		problem1 = Processor.parseFile(new File(this.getClass()
										 .getClassLoader()
										 .getResource("100.corecstrs.readable.smt2")
										 .getFile()));
		problem2 = Processor.parseFile(new File(this.getClass()
													.getClassLoader()
													.getResource("101.corecstrs.readable.smt2")
													.getFile()));
		problem3 = Processor.parseFile(new File(this.getClass()
													.getClassLoader()
													.getResource("103.corecstrs.readable.smt2")
													.getFile()));
		problem4 = Processor.parseFile(new File(this.getClass()
													.getClassLoader()
												 	.getResource("110.corecstrs.readable.smt2")
												 	.getFile()));
		p5 = Processor.parseFile(new File(this.getClass()
																								.getClassLoader()
																								.getResource("concat-036.smt2")
																								.getFile()));
		p6 = Processor.parseFile(new File(this.getClass()
																								.getClassLoader()
																								.getResource("concat-037.smt2")
																								.getFile()));
		p7 = Processor.parseFile(new File(this.getClass()
																																																				 .getClassLoader()
																																																				 .getResource("endswith-004.smt2")
																																																				 .getFile()));
		p8 = Processor.parseFile(new File(this.getClass()
																								.getClassLoader()
																								.getResource("startswith-004.smt2")
																								.getFile()));

	}

	@Test
	public void p1Andp3EqualsTest(){
		boolean res = Processor.compareProblems(problem1, problem3);
		assertTrue(res);
	}

	@Test
	public void p1Andp2EqualsTest(){
		assertTrue(Processor.compareProblems(problem1, problem2));
	}

	@Test
	public void p1Andp4NotEqualsTest(){
		assertFalse(Processor.compareProblems(problem1, problem4));
	}

	@Test
	public void p5Andp6NotEqualsTest(){
		assertFalse(Processor.compareProblems(p5, p6));
	}

	@Test
	public void p7Andp8NotEqualsTest(){
		assertFalse(Processor.compareProblems(p7, p8));
	}
}
