package structuralEquivalence;

import com.google.common.collect.Maps;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.smtlib.SMT;
import structuralEquivalence.expressionVisitor.OperatorStatistics;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.logging.Logger;

public class StructuralEquivalenceCheck {

	Logger logger = Logger.getLogger("Main");

	private List<ProblemInstance> knownProblems = new ArrayList<>();

	public static void main(String args[]){
		CommandLineParser parser = new DefaultParser();
		try {
			CommandLine cmd = parser.parse(setupOptions(), args);
			(new StructuralEquivalenceCheck()).runProgram(cmd);
		}
		catch (ParseException e) {
			e.printStackTrace();
		}

	}

	private void runProgram(CommandLine cmd){
		String smtFolder = cmd.getOptionValue("smt");
		File smtFolderFile = new File(smtFolder);
		if (smtFolderFile.exists()){
			Scanner collectedSMTFiles = new Scanner(smtFolderFile);
			for(File f: collectedSMTFiles.getCollectedFiles()){
				checkSMTFile(f);
			}
			System.out.println(generateReport());

			HashMap<String, Integer> data = new HashMap<>();
			OperatorStatistics statistics = new OperatorStatistics();
			for(ProblemInstance unique: knownProblems){
				try {
					unique.problem.getAllAssertionsAsConjunction().accept(statistics, data);
				} catch(Throwable e){
					System.out.println("Cannot get statistics from: " + unique.problemLocation.getAbsolutePath());
					e.printStackTrace();
				}
			}
			System.out.println("---Begin OperatorStatistics: ---");
			System.out.println(data);
			System.out.println("---End OperatorStatistics ---");
		}else{
			logger.severe(smtFolder + " does not exist. Terminate without analysis.");
		}
	}

	private void checkSMTFile(File smtFile){
		try {
			SMTProblem problem = Processor.parseFile(smtFile);
			for (ProblemInstance known : knownProblems) {

				if (Processor.compareProblems(problem, known.problem)) {
					known.addEquivalentProblem(smtFile);
					return;
				}

			}
			knownProblems.add(new ProblemInstance(problem, smtFile));
		}catch(Throwable e){
				System.out.println(String.format("Cought an exception checking: %s", smtFile));
				e.printStackTrace();
		}
	}

	private String generateReport(){
		StringBuilder a = new StringBuilder();
		for(ProblemInstance i: knownProblems){
			a.append(i.problemLocation.getPath());
			a.append("\t");
			a.append(i.equivalentProblems.size() + 1);
			a.append("\t[");

			for(File f: i.equivalentProblems){
				a.append(f.getPath());
				a.append(", ");
			}
			a.append("]\n");
		}
		return a.toString();
	}

	private static Options setupOptions(){

		Option smtRootFolder = Option.builder("smt").longOpt("smt root folder").hasArg().required().build();

		Options checkerOptions = new Options();

		checkerOptions.addOption(smtRootFolder);
		return  checkerOptions;
	}

	class ProblemInstance{
		public SMTProblem problem;
		public File problemLocation;
		public List<File> equivalentProblems;

		public ProblemInstance(SMTProblem problem, File location){
			this.problem = problem;
			this.problemLocation = location;
			this.equivalentProblems = new LinkedList<>();
		}

		public void addEquivalentProblem(File other){
			equivalentProblems.add(other);
		}
	}
}
