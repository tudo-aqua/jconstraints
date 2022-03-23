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

package gov.nasa.jpf.constraints.serialization;

import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.math.BigInteger;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("serialization")
public class ExpressionSerializationTest {

  @Test
  public void roundTripPropositionalCompoundTest() throws IOException, ClassNotFoundException {
    Variable<Boolean> a = Variable.create(BuiltinTypes.BOOL, "a");
    Variable<Boolean> b = Variable.create(BuiltinTypes.BOOL, "b");

    PropositionalCompound pc = PropositionalCompound.create(a, LogicalOperator.EQUIV, b);
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(pc);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    Object read = in.readObject();
    assertEquals(read.getClass(), PropositionalCompound.class);
    assertEquals(read.toString(), pc.toString());
  }

  @Test
  public void runStringSerializationExample1Test() throws IOException, ClassNotFoundException {
    Variable<String> str1 = Variable.create(BuiltinTypes.STRING, "_string0");
    Constant<BigInteger> cInt0 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(0));
    Expression<Boolean> lessThan =
        NumericBooleanExpression.create(
            cInt0, NumericComparator.LT, StringIntegerExpression.createLength(str1));
    Negation neg = Negation.create(ExpressionUtil.and(lessThan, lessThan));
    Expression<Boolean> finalExpr = ExpressionUtil.and(ExpressionUtil.TRUE, neg);
    finalExpr = ExpressionUtil.and(finalExpr, ExpressionUtil.TRUE);
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(finalExpr);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    Object read = in.readObject();
    assertEquals(read.getClass(), PropositionalCompound.class);
    assertEquals(read.toString(), finalExpr.toString());
  }

  @Test
  public void valuationSerializationTest() throws IOException, ClassNotFoundException {
    Valuation val = new Valuation();
    Variable<String> str1 = new Variable<>(BuiltinTypes.STRING, "_string1");
    val.setValue(str1, "haha");
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(val);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    Valuation readVal = (Valuation) in.readObject();
    assertEquals(readVal.getValue(str1), val.getValue(str1));
  }

  @Test
  public void stringIntegerExpressionSerializationTest()
      throws IOException, ClassNotFoundException {
    Variable<String> v = Variable.create(BuiltinTypes.STRING, "a");
    Constant<String> c = Constant.create(BuiltinTypes.STRING, "ab");
    StringIntegerExpression sie = StringIntegerExpression.createIndexOf(v, c);
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(sie);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    StringIntegerExpression readVal = (StringIntegerExpression) in.readObject();
    assertEquals(sie.getChildren().length, 3);
    assertEquals(readVal.getChildren().length, 3);
  }
}
