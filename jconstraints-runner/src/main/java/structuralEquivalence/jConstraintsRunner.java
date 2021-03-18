package structuralEquivalence;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider;
import gov.nasa.jpf.constraints.solvers.encapsulation.ProcessWrapperSolver;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.smtlib.impl.Command;

import java.io.File;

public class jConstraintsRunner {

	public static void main(String args[]){
		CommandLineParser parser = new DefaultParser();
		try {
			CommandLine cmd = parser.parse(setupOptions(), args);
			(new jConstraintsRunner()).runProgram(cmd);
		}
		catch (ParseException e) {
			e.printStackTrace();
		}
	}

	private void runProgram(CommandLine cmd){
		String filepath = cmd.getOptionValue("smt");
		String solver = cmd.getOptionValue("s");
		if  (solver.equalsIgnoreCase("z3")
				 || solver.equalsIgnoreCase("cvc4")
				 || solver.equalsIgnoreCase("multi")){
			ConstraintSolverFactory factory = ConstraintSolverFactory.getRootFactory();
			ConstraintSolver constraintSolver;
			if(solver.equalsIgnoreCase("cvc4")){
				constraintSolver = new ProcessWrapperSolver("cvc4");
			}else{
				constraintSolver = factory.createSolver(solver);
			}
			SMTProblem problem = Processor.parseFile(new File(filepath));
			Valuation val = new Valuation();
			ConstraintSolver.Result res = constraintSolver.solve(problem.getAllAssertionsAsConjunction(), val);
			System.out.println("RESULT: " + res);
			if(res == ConstraintSolver.Result.SAT){
				boolean evaluated = false;
				try {
					System.out.println("Valuation: " +val.toString());
				 evaluated=problem.getAllAssertionsAsConjunction().evaluateSMT(val);
				}catch (Throwable t){
					t.printStackTrace();
					System.out.println("VALUATIONERROR");
				}
				System.out.println("EVALUATED: " + evaluated);
			}
		}
		System.exit(0);
	}

	private static Options setupOptions(){

		Option smtRootFolder = Option.builder("smt").longOpt("smt_file").hasArg().required().build();
		Option solver = Option.builder("s").longOpt("solver").hasArg().required().build();

		Options checkerOptions = new Options();

		checkerOptions.addOption(smtRootFolder);
		checkerOptions.addOption(solver);
		return  checkerOptions;
	}

}
