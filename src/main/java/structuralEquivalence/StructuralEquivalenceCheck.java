package structuralEquivalence;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import java.io.File;
import java.util.logging.Logger;

public class StructuralEquivalenceCheck {

	Logger logger = Logger.getLogger("Main");

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

		}else{
			logger.severe(smtFolder + " does not exist. Terminate without analysis.");
		}
	}



	private static Options setupOptions(){

		Option smtRootFolder = Option.builder("smt").longOpt("smt root folder").hasArg().required().build();

		Options checkerOptions = new Options();

		checkerOptions.addOption(smtRootFolder);
		return  checkerOptions;
	}
}
