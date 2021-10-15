/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
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

package io.github.tudoaqua.jconstraints.cvc4;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.smtlibUtility.smtsolver.SMTCMDSolver;
import io.github.tudoaqua.jconstraints.cvc4.exception.CVC4SMTCMDInitializationException;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.attribute.PosixFilePermission;
import java.nio.file.attribute.PosixFilePermissions;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;

public class CVC4SMTCMDSolver extends SMTCMDSolver implements UNSATCoreSolver {
  static final String UNSAT_CORE_EXTENSION = " --produce-unsat-cores";
  private static final String flags = " -L smt -m --strings-exp";
  private File tmpFolder;

  public CVC4SMTCMDSolver() {
    super(resolveCVC4Command(), false);
    smtExportConfig.replaceZ3Escape = true;
  }

  public CVC4SMTCMDSolver(long timeout) {
    super(resolveCVC4Command(), false, timeout);
    smtExportConfig.replaceZ3Escape = true;
    super.init();
  }

  @Override
  public SolverContext createContext() {
    String[] cxtCommand = splitCMD(super.solverCommand + " --incremental");
    CVC4SMTCMDContext ctx =
        solverTimeOut < 0
            ? new CVC4SMTCMDContext(cxtCommand, smtExportConfig)
            : new CVC4SMTCMDContext(cxtCommand, smtExportConfig, solverTimeOut);
    if (super.isUnsatCoreSolver) {
      ctx.enableUnsatTracking();
    }
    return ctx;
  }

  @Override
  public void enableUnsatTracking() {
    super.solverCommand += UNSAT_CORE_EXTENSION;
    super.smtExportConfig.namedAssert = true;
    super.isUnsatCoreSolver = true;
  }

  @Override
  public List<Expression<Boolean>> getUnsatCore() {
    return super.unsatCoreLastRun;
  }

  private static String resolveCVC4Command() {
    String os = System.getProperty("os.name").replaceAll(" ", "").toLowerCase(Locale.ROOT);
    String arch = System.getProperty("os.arch");
    if (!(arch.equals("x86_64") || arch.equals("amd64"))) {
      throw new IllegalArgumentException(
          "There are no other architectures supported than AMD64 or x86_64 at the moment. Found: "
              + arch);
    }
    String binaryName = "";
    try {
      Path cvcPath;
      if (os.contains("osx")) {
        Path tmpDir =
            Files.createTempDirectory(
                "cvc4files", PosixFilePermissions.asFileAttribute(getPermissions()));
        tmpDir.toFile().deleteOnExit();
        String libcvc4 = "libcvc4.7.dylib";
        Path cvc4Dylib = Paths.get(tmpDir.toAbsolutePath().toString(), libcvc4);
        String libcvc4parser = "libcvc4parser.7.dylib";
        Path cvc4parserDylib = Paths.get(tmpDir.toAbsolutePath().toString(), libcvc4parser);
        copy(libcvc4, cvc4Dylib);
        copy(libcvc4parser, cvc4parserDylib);
        binaryName = "cvc4-osx-amd64";
        cvcPath = Paths.get(tmpDir.toAbsolutePath().toString(), binaryName);

      } else if (os.contains("win")) {
        throw new IllegalArgumentException(
            "CVC4 is not supproted as JConstraints backend on windows");
      } else {
        binaryName = "cvc4-linux-amd64";
        cvcPath =
            Files.createTempFile(
                "cvc4", "", PosixFilePermissions.asFileAttribute(getPermissions()));
        cvcPath.toFile().deleteOnExit();
      }
      copy(binaryName, cvcPath);
      return cvcPath.toFile().getAbsolutePath() + flags;
    } catch (IOException e) {
      CVC4SMTCMDInitializationException execp = new CVC4SMTCMDInitializationException();
      execp.addSuppressed(e);
      throw execp;
    }
  }

  private static void copy(String ressourceName, Path outPath) throws IOException {
    try (InputStream binStream =
            ClassLoader.getSystemClassLoader().getResourceAsStream(ressourceName);
        OutputStream out = Files.newOutputStream(outPath)) {
      final byte[] buffer = new byte[1 << 13];
      int read;
      while ((read = binStream.read(buffer, 0, buffer.length)) >= 0) {
        out.write(buffer, 0, read);
      }
    }
    Files.setPosixFilePermissions(outPath, getPermissions());
  }

  private static Set<PosixFilePermission> getPermissions() {
    HashSet<PosixFilePermission> perms = new HashSet();
    perms.add(PosixFilePermission.OWNER_WRITE);
    perms.add(PosixFilePermission.OWNER_READ);
    perms.add(PosixFilePermission.OWNER_EXECUTE);
    return perms;
  }
}
