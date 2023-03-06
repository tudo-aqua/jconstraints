/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2023 The jConstraints Authors
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

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
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
import java.util.Map;
import java.util.concurrent.ExecutionException;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import structuralEquivalence.expressionVisitor.OperatorStatistics;
import tools.datastructure.UsedOperations;

public class OperationsCounterII {

  public OperationsCounterII() {}

  public static void main(String[] args) {
    CommandLineParser parser = new DefaultParser();
    try {
      CommandLine cmd = parser.parse(setupOptions(), args);
      (new OperationsCounterII()).runProgram(cmd);
    } catch (ParseException | IOException | InterruptedException | ExecutionException e) {
      e.printStackTrace();
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

    Options checkerOptions = new Options();

    checkerOptions.addOption(smtRootFolder);
    checkerOptions.addOption(resultRootFolder);
    checkerOptions.addOption(limit);
    return checkerOptions;
  }

  private void runProgram(CommandLine cmd)
      throws IOException, InterruptedException, ExecutionException {
    String path = cmd.getOptionValue("folder");
    PathMatcher folderPrefix = FileSystems.getDefault().getPathMatcher("glob:**.smt2");
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
          final int counter = 0;

          public FileVisitResult visitFile(Path file, BasicFileAttributes attrs)
              throws IOException {
            if (folderPrefix.matches(file)) {
              System.out.println(String.format("Processing: %s", file.toString()));
              UsedOperations uo = countOperations(file);
              if (uo != null) {
                writeResult(cmd.getOptionValue("result"), uo);
              }
            }
            if (limited && counter > limit) {
              return FileVisitResult.TERMINATE;
            }
            return FileVisitResult.CONTINUE;
          }
        });
  }

  private UsedOperations countOperations(Path file) {
    SMTProblem problem = null;
    try {
      problem = SMTLIBParser.parseSMTProgramFromFile(file.toString());
      OperatorStatistics visitor = new OperatorStatistics();
      HashMap<String, Integer> data = new HashMap<>();
      problem.assertions.forEach(
          a -> {
            int asserts = data.getOrDefault("assert", 0);
            asserts++;
            data.put("assert", asserts);
            a.accept(visitor, data);
          });
      data.put("variable", problem.variables.size());
      return new UsedOperations(file.toString(), data);
    } catch (Exception e) {
      System.out.println(
          "Problem parsing: "
              + file
              + " "
              + (e.getMessage() == null ? e.toString() : e.getMessage()));
    }
    return null;
  }

  private void writeResult(String resultFolder, UsedOperations result) throws IOException {
    HashMap<String, Integer> overall = new HashMap<>();
    if (resultFolder != null) {
      Files.createDirectories(Paths.get(resultFolder));
    }
    Path problem = Paths.get(result.file);
    Path resultFile =
        Paths.get(resultFolder, problem.getFileName().toString().replace("smt2", "out"));
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
}
