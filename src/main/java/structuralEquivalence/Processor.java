package structuralEquivalence;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import org.smtlib.IParser;
import org.smtlib.SMT;
import structuralEquivalence.expressionVisitor.EquivalenceVisitor;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

public class Processor {

	public static SMTProblem parseFile(File smtFile){
		try(BufferedReader reader = new BufferedReader(new FileReader(smtFile))){
			String fileContent = reader.lines().reduce("", (a, b) -> a + b);
			return SMTLIBParser.parseSMTProgram(fileContent);
		}
		catch (IOException | SMTLIBParserException | IParser.ParserException e) {
			e.printStackTrace();
			throw new RuntimeException(e);
		}
	}

	public static boolean compareProblems(SMTProblem problemA, SMTProblem problemB){
		EquivalenceVisitor visitor = new EquivalenceVisitor();
		return problemA.getAllAssertionsAsConjunction().accept(visitor, problemB.getAllAssertionsAsConjunction());
	}
}
