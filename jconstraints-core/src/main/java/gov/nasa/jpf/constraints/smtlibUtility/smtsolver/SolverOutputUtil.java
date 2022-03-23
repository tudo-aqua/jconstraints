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

package gov.nasa.jpf.constraints.smtlibUtility.smtsolver;

import static java.util.concurrent.TimeUnit.MILLISECONDS;

import com.google.common.util.concurrent.SimpleTimeLimiter;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportGenContext;
import java.io.BufferedReader;
import java.util.UUID;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeoutException;

public class SolverOutputUtil {

  private static final ExecutorService threadExecutor;
  private static final SimpleTimeLimiter timeLimiter;
  private static final long defaultTimeout = 500;

  static {
    threadExecutor = Executors.newCachedThreadPool();
    timeLimiter = SimpleTimeLimiter.create(threadExecutor);
    Runtime.getRuntime()
        .addShutdownHook(
            new Thread() {
              public void run() {
                threadExecutor.shutdownNow();
              }
            });
  }

  public static String readProcessOutput(SMTLibExportGenContext context, BufferedReader processOut)
      throws ExecutionException, InterruptedException, TimeoutException {
    return readProcessOutput(context, processOut, defaultTimeout);
  }

  public static String readProcessOutput(
      SMTLibExportGenContext context, BufferedReader processOut, long milliseconds)
      throws ExecutionException, InterruptedException, TimeoutException {
    StringBuilder output = new StringBuilder();
    String line;
    // echo does not work if a number is in front
    String uid = "a" + UUID.randomUUID();
    boolean matchedUid = false;

    Callable<String> readLineCallable = processOut::readLine;

    context.echo(uid);
    while (!matchedUid
        && (line = timeLimiter.callWithTimeout(readLineCallable, milliseconds, MILLISECONDS))
            != null) {
      matchedUid = line.equals(uid);
      output.append(line);
      output.append("\n");
    }
    String outputString = output.toString();
    if (outputString.contains("Parse Error")) {
      throw new IllegalStateException("Parse Error:\n" + output);
    }
    if (!matchedUid) {
      throw new IllegalStateException("Incomplete Output (Did not match UID)");
    }
    return outputString.replace(uid, "").trim();
  }
}
