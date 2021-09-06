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

package gov.nasa.jpf.constraints.smtlibUtility.solver;

import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BitLimitedBVIntegerType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.PrintStream;
import java.util.LinkedList;
import java.util.List;

public class SMTLibExportGenContext {

  private class VarContext {

    private final VarContext next;

    private final List<Variable> defined = new LinkedList<>();

    private final List<Variable> pending = new LinkedList<>();

    private VarContext(VarContext next) {
      this.next = next;
    }

    private boolean isDefined(Variable var) {
      return defined.contains(var)
          || pending.contains(var)
          || (next != null && next.isDefined(var));
    }

    private void add(Variable var) {
      if (!isDefined(var)) {
        pending.add(var);
      }
    }

    private void addLocal(Variable var) {
      defined.add(var);
    }

    private void flush() {
      for (Variable v : pending) {
        out.println("(declare-const " + v.getName() + " " + type(v) + ")");
        defined.add(v);
      }
      pending.clear();
    }
  }

  private int statementLevel = 0;

  private final PrintStream out;

  private StringBuilder statementBuffer = new StringBuilder();

  private VarContext varContext = new VarContext(null);

  public SMTLibExportGenContext(PrintStream out) {
    this.out = out;
  }

  void appendVar(Variable<?> var) {
    varContext.add(var);
    statementBuffer.append(" " + var.getName());
  }

  void appendLocalVarDecl(Variable v) {
    varContext.addLocal(v);
    statementBuffer.append(" (" + v.getName() + " " + type(v) + ")");
  }

  void registerLocalSymbol(Variable v) {
    varContext.addLocal(v);
  }

  void append(String s) {
    statementBuffer.append(" ");
    statementBuffer.append(s);
  }

  void open(String s) {
    if (statementLevel > 0) {
      statementBuffer.append(" ");
    }
    statementBuffer.append("(");
    statementBuffer.append(s);
    statementLevel++;
  }

  void close() {
    statementBuffer.append(")");
    statementLevel--;
    if (statementLevel < 0) {
      throw new IllegalStateException(
          "More brackets closed than opened. statementLevel >= 0 must be invariant in this"
              + " Program.");
    }
  }

  void push() {
    this.varContext.flush();
    out.println("(push)");
    this.varContext = new VarContext(this.varContext);
  }

  void pop(int n) {
    for (int i = 0; i < n; i++) {
      out.println("(pop)");
      if (this.varContext.next != null) {
        this.varContext = this.varContext.next;
      }
    }
  }

  public void solve() {
    out.println("(check-sat)");
    out.flush();
  }

  public void flush() {
    this.varContext.flush();
    out.println(statementBuffer.toString());
    statementBuffer = new StringBuilder();
  }

  private String type(Variable v) {
    // TODO: add missing data types
    if (BuiltinTypes.BOOL.equals(v.getType())) {
      return "Bool";
    } else if (BuiltinTypes.SINT32.equals(v.getType())) {
      return "(_ BitVec 32)";
    } else if (BuiltinTypes.UINT16.equals(v.getType())) {
      return "(_ BitVec 16)";
    } else if (BuiltinTypes.SINT8.equals(v.getType())) {
      return "(_ BitVec 8)";
    } else if (BuiltinTypes.STRING.equals(v.getType())) {
      return "String";
    } else if (BuiltinTypes.INTEGER.equals(v.getType())) {
      return "Int";
    } else if (v.getType() instanceof BitLimitedBVIntegerType) {
      return "(_ BitVec " + ((BitLimitedBVIntegerType) v.getType()).getNumBits() + ")";
    }
    throw new IllegalArgumentException("Unsupported type: " + v.getType());
  }
}
