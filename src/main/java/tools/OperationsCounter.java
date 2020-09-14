package tools;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import tools.callables.OperatorAnalysisTask;
import tools.datastructure.UsedOperations;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

public class OperationsCounter {

	ExecutorService pool;
	List<Future<UsedOperations>> tasks;

	public OperationsCounter(){
		int usedCores = Runtime.getRuntime().availableProcessors() - 2;
		pool = Executors.newWorkStealingPool(Runtime.getRuntime().availableProcessors() - 2);
		tasks = new LinkedList<>();
		System.out.println(String.format("Created Work-Stealing Pool with %d cores",usedCores));
	}

	public static void main(String args[]){
		CommandLineParser parser = new DefaultParser();
		try {
			CommandLine cmd = parser.parse(setupOptions(), args);
			(new OperationsCounter()).runProgram(cmd);
		}
		catch (ParseException | IOException | InterruptedException | ExecutionException e) {
			e.printStackTrace();
		}

	}

	private void runProgram(CommandLine cmd) throws IOException, InterruptedException, ExecutionException {
		String path = cmd.getOptionValue("folder");
		PathMatcher folderPrefix = FileSystems.getDefault().getPathMatcher( "glob:**.smt2");
		Files.walkFileTree(Paths.get(path), new SimpleFileVisitor<Path>(){
			public FileVisitResult visitFile(Path file, BasicFileAttributes attrs){
				if(folderPrefix.matches(file)){
					Future<UsedOperations> result = pool.submit(new OperatorAnalysisTask(file.toAbsolutePath().toString()));
					tasks.add(result);
				}
				return FileVisitResult.CONTINUE;
			}
		});
		pool.shutdown();
		pool.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
		computeResult(cmd.getOptionValue("result"));
	}

	private void computeResult(String resultFolder) throws ExecutionException, InterruptedException, IOException {
		HashMap<String, Integer> overall = new HashMap<>();
		Files.createDirectories(Paths.get(resultFolder));
		for(Future task: tasks){
			UsedOperations result = (UsedOperations) task.get();
			if (result == null){
				continue;
			}
			Path problem = Paths.get(result.file);
			Path resultFile = Paths.get(resultFolder, problem.getFileName().toString());
			Files.createDirectories(Paths.get(resultFolder, problem.getFileName().toString()));
			try(PrintWriter resultWriter = new PrintWriter(resultFile.toFile())){
				for(Map.Entry<String,Integer> e: result.operators.entrySet()){
					resultWriter.println(String.format("Operator: {} occurs: {}", e.getKey(), e.getValue()));
					int old = overall.getOrDefault(e.getKey(), 0);
					overall.put(e.getKey(), old + e.getValue());
				}
			}catch (IOException e){
				e.printStackTrace();
			}
		}

		Path overallPath = Paths.get(resultFolder, "overall.txt");
		try(PrintWriter overallResult = new PrintWriter(overallPath.toFile())){
			for(Map.Entry<String, Integer> e: overall.entrySet()){
				overallResult.println(String.format("Operator: {} occurs: {}", e.getKey(), e.getValue()));
			}
		}
	}

	private static Options setupOptions(){

		Option smtRootFolder = Option.builder("f").longOpt("folder").desc("smt root folder").hasArg().required().build();
		Option resultRootFolder = Option.builder("r").longOpt("result").desc("result root folder").hasArg().required().build();

		Options checkerOptions = new Options();

		checkerOptions.addOption(smtRootFolder);
		checkerOptions.addOption(resultRootFolder);
		return  checkerOptions;
	}
}
