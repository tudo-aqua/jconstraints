/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2022 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package tools;

import java.io.IOException;
import java.io.PrintWriter;
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
import java.util.concurrent.TimeUnit;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import tools.callables.OperatorAnalysisTask;
import tools.datastructure.UsedOperations;

public class OperationsCounter {

  ExecutorService pool;
  List<Future<UsedOperations>> tasks;

  public OperationsCounter() {
    int usedCores = Runtime.getRuntime().availableProcessors() - 2;
    pool = Executors.newWorkStealingPool(Runtime.getRuntime().availableProcessors() - 2);
    tasks = new LinkedList<>();
    System.out.println(String.format("Created Work-Stealing Pool with %d cores", usedCores));
  }

  public static void main(String args[]) {
    CommandLineParser parser = new DefaultParser();
    try {
      CommandLine cmd = parser.parse(setupOptions(), args);
      (new OperationsCounter()).runProgram(cmd);
    } catch (ParseException | IOException | InterruptedException | ExecutionException e) {
      e.printStackTrace();
    }
  }

  private void runProgram(CommandLine cmd)
      throws IOException, InterruptedException, ExecutionException {
    String path = cmd.getOptionValue("folder");
    String fileEnding = cmd.hasOption("smt-ending") ? cmd.getOptionValue("smt-ending") : "smt2";
    PathMatcher folderPrefix = FileSystems.getDefault().getPathMatcher("glob:**." + fileEnding);
    boolean limited = cmd.hasOption("limit");
    final int limit;
    if (limited) {
      limit = Integer.valueOf(cmd.getOptionValue("limit"));
    } else {
      limit = 0;
    }
    int counter = 0;
    Files.walkFileTree(
        Paths.get(path),
        new SimpleFileVisitor<Path>() {
          int counter = 0;

          public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
            if (folderPrefix.matches(file)) {
              Future<UsedOperations> result =
                  pool.submit(new OperatorAnalysisTask(file.toAbsolutePath().toString()));
              tasks.add(result);
              ++counter;
            }
            if (limited && counter > limit) {
              return FileVisitResult.TERMINATE;
            }
            return FileVisitResult.CONTINUE;
          }
        });
    pool.shutdown();
    pool.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
    computeResult(cmd.getOptionValue("result"), cmd.getOptionValue("smt-ending", ""));
  }

  private void computeResult(String resultFolder, String smt)
      throws ExecutionException, InterruptedException, IOException {
    HashMap<String, Integer> overall = new HashMap<>();
    if (resultFolder != null) {
      Files.createDirectories(Paths.get(resultFolder));
    }
    for (Future task : tasks) {
      UsedOperations result = (UsedOperations) task.get();
      if (result == null) {
        continue;
      }
      Path problem = Paths.get(result.file);
      String resultFileName = problem.getFileName().toString().replace("smt2", "out");
      if (!smt.equals("")) {
        resultFileName = problem.getFileName().toString().replace(smt, "out");
      }
      Path resultFile = Paths.get(resultFolder, resultFileName);
      System.out.println("Writting result: " + resultFile);
      try (PrintWriter resultWriter = new PrintWriter(resultFile.toFile())) {
        for (Map.Entry<String, Integer> e : result.operators.entrySet()) {
          resultWriter.println(String.format("%s\t%d", e.getKey(), e.getValue()));
          int old = overall.getOrDefault(e.getKey(), 0);
          overall.put(e.getKey(), old + e.getValue());
        }
      } catch (IOException e) {
        e.printStackTrace();
      }
    }

    Path overallPath = Paths.get(resultFolder, "overall.txt");
    try (PrintWriter overallResult = new PrintWriter(overallPath.toFile())) {
      for (Map.Entry<String, Integer> e : overall.entrySet()) {
        overallResult.println(String.format("Operator: %s occurs: %d", e.getKey(), e.getValue()));
      }
    }
  }

  private static Options setupOptions() {

    Option smtRootFolder =
        Option.builder("f").longOpt("folder").desc("smt root folder").hasArg().required().build();
    Option resultRootFolder =
        Option.builder("r")
            .longOpt("result")
            .desc("result root folder")
            .hasArg()
            .required()
            .build();
    Option limit =
        Option.builder("n")
            .longOpt("limit")
            .desc("A maximum Number of procesed files")
            .hasArg()
            .optionalArg(true)
            .build();
    Option smt =
        Option.builder("e")
            .longOpt("smt-ending")
            .desc("use .smt instead of .smt2 as file ending")
            .hasArg()
            .optionalArg(true)
            .build();

    Options checkerOptions = new Options();

    checkerOptions.addOption(smtRootFolder);
    checkerOptions.addOption(resultRootFolder);
    checkerOptions.addOption(limit);
    checkerOptions.addOption(smt);
    return checkerOptions;
  }
}
