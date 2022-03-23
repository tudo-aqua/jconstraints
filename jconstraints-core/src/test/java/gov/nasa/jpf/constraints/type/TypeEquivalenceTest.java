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

package gov.nasa.jpf.constraints.type;

import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.BuiltinTypes.BoolType;
import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("types")
public class TypeEquivalenceTest {

  @Test
  public void booleanTypeTest() throws IOException, ClassNotFoundException {
    Constant<Boolean> c0 = Constant.create(new BoolType(), true);
    Type<Boolean> t = c0.getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);

    Constant<Boolean> c1 = (Constant<Boolean>) serializeAndDeserialize(c0);
    t = c1.getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);

    Constant<Boolean> c2 = (Constant<Boolean>) serializeAndDeserialize(ExpressionUtil.TRUE);
    t = c2.getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);

    Constant<Boolean> c3 = (Constant<Boolean>) serializeAndDeserialize(ExpressionUtil.FALSE);
    t = c3.getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);
  }

  private Expression<Boolean> serializeAndDeserialize(Expression<Boolean> expr)
      throws IOException, ClassNotFoundException {
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(expr);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    Object read = in.readObject();
    return (Expression<Boolean>) read;
  }

  @Test
  public void booleanType2Test() throws IOException, ClassNotFoundException {
    Variable<Boolean> a = Variable.create(BuiltinTypes.BOOL, "a");
    Variable<Boolean> b = Variable.create(BuiltinTypes.BOOL, "b");
    PropositionalCompound pc = PropositionalCompound.create(a, LogicalOperator.EQUIV, b);

    PropositionalCompound pc1 = (PropositionalCompound) serializeAndDeserialize(pc);
    Type<Boolean> t = pc1.getLeft().getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);

    t = pc1.getRight().getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);
  }

  @Test
  public void booleanVarType2Test() throws IOException, ClassNotFoundException {
    Variable<Boolean> a = Variable.create(BuiltinTypes.BOOL, "a");

    Variable<Boolean> a1 = (Variable<Boolean>) serializeAndDeserialize(a);
    Type<Boolean> t = a1.getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);
  }
}
