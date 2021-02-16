package tools.callables;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import org.smtlib.IParser;
import structuralEquivalence.expressionVisitor.OperatorStatistics;
import tools.datastructure.UsedOperations;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.concurrent.Callable;

public class OperatorAnalysisTask implements Callable<UsedOperations> {

	private String file;
	public OperatorAnalysisTask(String file){
		this.file = file;
	}

	@Override
	public UsedOperations call() throws IOException {
		SMTProblem problem = null;
		try {
			problem = SMTLIBParser.parseSMTProgram(new String(Files.readAllBytes(Paths.get(file))));
			OperatorStatistics visitor = new OperatorStatistics();
			HashMap<String, Integer> data = new HashMap<>();
			problem.assertions.forEach(a -> {
				int asserts = data.getOrDefault("assert", 0);
				asserts++;
				data.put("assert", asserts);
				a.accept(visitor, data);
			});
			return new UsedOperations(file, data);
		}
		catch (Exception e) {
			System.out.println("Problem parsing: " + file + " " + (e.getMessage() == null? e.toString(): e.getMessage()));
		}
		return null;
	}
}
