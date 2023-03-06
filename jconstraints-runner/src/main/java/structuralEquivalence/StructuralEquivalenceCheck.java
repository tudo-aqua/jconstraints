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

package structuralEquivalence;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.logging.Logger;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import structuralEquivalence.expressionVisitor.OperatorStatistics;

public class StructuralEquivalenceCheck {

  Logger logger = Logger.getLogger("Main");

  private List<ProblemInstance> knownProblems = new ArrayList<>();

  public static void main(String args[]) {
    CommandLineParser parser = new DefaultParser();
    try {
      CommandLine cmd = parser.parse(setupOptions(), args);
      (new StructuralEquivalenceCheck()).runProgram(cmd);
    } catch (ParseException e) {
      e.printStackTrace();
    }
  }

  private void runProgram(CommandLine cmd) {
    String smtFolder = cmd.getOptionValue("smt");
    File smtFolderFile = new File(smtFolder);
    if (smtFolderFile.exists()) {
      Scanner collectedSMTFiles = new Scanner(smtFolderFile);
      for (File f : collectedSMTFiles.getCollectedFiles()) {
        checkSMTFile(f);
      }
      System.out.println(generateReport());

      HashMap<String, Integer> data = new HashMap<>();
      OperatorStatistics statistics = new OperatorStatistics();
      for (ProblemInstance unique : knownProblems) {
        try {
          unique.problem.getAllAssertionsAsConjunction().accept(statistics, data);
        } catch (Throwable e) {
          System.out.println(
              "Cannot get statistics from: " + unique.problemLocation.getAbsolutePath());
          e.printStackTrace();
        }
      }
      System.out.println("---Begin OperatorStatistics: ---");
      System.out.println(data);
      System.out.println("---End OperatorStatistics ---");
    } else {
      logger.severe(smtFolder + " does not exist. Terminate without analysis.");
    }
  }

  private void checkSMTFile(File smtFile) {
    try {
      SMTProblem problem = Processor.parseFile(smtFile);
      for (ProblemInstance known : knownProblems) {

        if (Processor.compareProblems(problem, known.problem)) {
          known.addEquivalentProblem(smtFile);
          return;
        }
      }
      knownProblems.add(new ProblemInstance(problem, smtFile));
    } catch (Throwable e) {
      System.out.println(String.format("Cought an exception checking: %s", smtFile));
      e.printStackTrace();
    }
  }

  private String generateReport() {
    StringBuilder a = new StringBuilder();
    for (ProblemInstance i : knownProblems) {
      a.append(i.problemLocation.getPath());
      a.append("\t");
      a.append(i.varCount);
      a.append("\t");
      a.append(i.equivalentProblems.size() + 1);
      a.append("\t[");

      for (File f : i.equivalentProblems) {
        a.append(f.getPath());
        a.append(", ");
      }
      a.append("]\n");
    }
    return a.toString();
  }

  private static Options setupOptions() {

    Option smtRootFolder =
        Option.builder("smt").longOpt("smt root folder").hasArg().required().build();

    Options checkerOptions = new Options();

    checkerOptions.addOption(smtRootFolder);
    return checkerOptions;
  }

  class ProblemInstance {
    public SMTProblem problem;
    public int varCount;
    public File problemLocation;
    public List<File> equivalentProblems;

    public ProblemInstance(SMTProblem problem, File location) {
      this.problem = problem;
      varCount = ExpressionUtil.freeVariables(problem.getAllAssertionsAsConjunction()).size();
      this.problemLocation = location;
      this.equivalentProblems = new LinkedList<>();
    }

    public void addEquivalentProblem(File other) {
      equivalentProblems.add(other);
    }
  }
}
