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

package gov.nasa.jpf.constraints.smtlibUtility.export;

import static gov.nasa.jpf.constraints.expressions.LogicalOperator.AND;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.EQUIV;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.IMPLY;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.OR;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.XOR;
import static gov.nasa.jpf.constraints.util.CharsetIO.toNormalizedStringUTF8;
import static gov.nasa.jpf.constraints.util.CharsetIO.wrapInUTF8PrintStream;
import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportWrapper;
import gov.nasa.jpf.constraints.solvers.dontknow.DontKnowSolver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("smt-export")
public class LogicalExpressionTest {
  Variable<Boolean> var1;
  Variable<Boolean> var2;

  SolverContext se;
  ByteArrayOutputStream baos;
  PrintStream ps;

  @BeforeEach
  public void initialize() {
    var1 = Variable.create(BuiltinTypes.BOOL, "x");
    var2 = Variable.create(BuiltinTypes.BOOL, "y");
    baos = new ByteArrayOutputStream();
    ps = wrapInUTF8PrintStream(baos);
    se = (new SMTLibExportWrapper(new DontKnowSolver(), ps)).createContext();
  }

  @Test
  public void PropositionalCompoundAndTest() {
    String expected =
        "(declare-const x Bool)\n" + "(declare-const y Bool)\n" + "(assert (and x y))\n";
    PropositionalCompound expr = PropositionalCompound.create(var1, AND, var2);
    se.add(expr);
    assertEquals(toNormalizedStringUTF8(baos), expected);
  }

  @Test
  public void PropositionalCompoundOrTest() {
    String expected =
        "(declare-const x Bool)\n" + "(declare-const y Bool)\n" + "(assert (or x y))\n";
    PropositionalCompound expr = PropositionalCompound.create(var1, OR, var2);
    se.add(expr);
    assertEquals(toNormalizedStringUTF8(baos), expected);
  }

  @Test
  public void PropositionalCompoundImplyTest() {
    String expected =
        "(declare-const x Bool)\n" + "(declare-const y Bool)\n" + "(assert (=> x y))\n";
    PropositionalCompound expr = PropositionalCompound.create(var1, IMPLY, var2);
    se.add(expr);
    assertEquals(toNormalizedStringUTF8(baos), expected);
  }

  @Test
  public void PropositionalCompoundEquivalentTest() {
    String expected =
        "(declare-const x Bool)\n" + "(declare-const y Bool)\n" + "(assert (= x y))\n";
    PropositionalCompound expr = PropositionalCompound.create(var1, EQUIV, var2);
    se.add(expr);
    assertEquals(toNormalizedStringUTF8(baos), expected);
  }

  @Test
  public void PropositionalXORAndTest() {
    String expected =
        "(declare-const x Bool)\n" + "(declare-const y Bool)\n" + "(assert (xor x y))\n";
    PropositionalCompound expr = PropositionalCompound.create(var1, XOR, var2);
    se.add(expr);
    assertEquals(toNormalizedStringUTF8(baos), expected);
  }

  @Test
  public void NegationTest() {
    String expected = "(declare-const x Bool)\n" + "(assert (not x))\n";
    Negation expr = Negation.create(var1);
    se.add(expr);
    assertEquals(toNormalizedStringUTF8(baos), expected);
  }

  @Test
  public void ifThenElseTest() {
    String expected =
        "(declare-const x Bool)\n"
            + "(declare-const y Bool)\n"
            + "(declare-const z Bool)\n"
            + "(assert (ite x y z))"
            + "\n";

    Variable<Boolean> var1 = Variable.create(BuiltinTypes.BOOL, "x");
    Variable<Boolean> var2 = Variable.create(BuiltinTypes.BOOL, "y");
    Variable<Boolean> var3 = Variable.create(BuiltinTypes.BOOL, "z");
    IfThenElse<Boolean> expr = IfThenElse.create(var1, var2, var3);
    se.add(expr);
    assertEquals(toNormalizedStringUTF8(baos), expected);
  }
}
