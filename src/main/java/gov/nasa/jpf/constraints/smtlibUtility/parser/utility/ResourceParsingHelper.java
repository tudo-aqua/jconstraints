/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * <p>This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * <p>Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377 the original license
 * is: Copyright (C) 2015, United States Government, as represented by the Administrator of the
 * National Aeronautics and Space Administration. All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment platform is licensed
 * under the Apache License, Version 2.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues under Apache
 * 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.smtlibUtility.parser.utility;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import java.io.File;
import java.io.IOException;
import java.util.Scanner;
import org.smtlib.IParser;

public class ResourceParsingHelper {

  public static File loadResource(final String resourceName) {
    final ClassLoader loader = ResourceParsingHelper.class.getClassLoader();
    return new File(loader.getResource(resourceName).getFile());
  }

  public static SMTProblem parseResourceFile(final String resourceName)
      throws IOException, SMTLIBParserException, IParser.ParserException {
    final ClassLoader loader = ResourceParsingHelper.class.getClassLoader();
    final File inputFile = loadResource(resourceName);

    final StringBuilder content = new StringBuilder();
    try (final Scanner inputScanner = new Scanner(inputFile)) {
      while (inputScanner.hasNextLine()) {
        content.append(inputScanner.nextLine());
      }
    }
    return SMTLIBParser.parseSMTProgram(content.toString());
  }
}
