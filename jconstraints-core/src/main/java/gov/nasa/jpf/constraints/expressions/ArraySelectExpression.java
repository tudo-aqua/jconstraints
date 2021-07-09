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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.ArrayType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import java.io.IOException;
import java.math.BigInteger;
import java.util.Collection;

public class ArraySelectExpression extends Expression {

  private final Expression arrayVariable;

  private final Expression index;

  public ArraySelectExpression(Expression arrayVariable, Expression index) {
    this.arrayVariable = arrayVariable;
    this.index = index;
  }

  public Expression getArrayVariable() {
    return arrayVariable;
  }

  public Expression getIndex() {
    return index;
  }

  @Override
  public Expression evaluate(Valuation values) {
    Expression arrayObject;
    if (arrayVariable instanceof Variable) {
      arrayObject = (Expression) values.getValue(((Variable) arrayVariable).getName());
    } else arrayObject = arrayVariable;
    ArrayExpression arrayExpression = null;
    if (!(arrayObject instanceof Variable)) {
      arrayExpression =
          arrayObject instanceof ArrayExpression
              ? (ArrayExpression) arrayObject
              : (ArrayExpression) arrayObject.evaluate(values);
    } else {
      arrayExpression = (ArrayExpression) arrayObject;
    }
    Constant conIndex = new Constant(index.getType(), index.evaluate(values));
    return (Expression) arrayExpression.getContent().get(conIndex);
  }

  @Override
  public Expression evaluateSMT(Valuation values) {
    Expression arrayObject;
    if (arrayVariable instanceof Variable) {
      arrayObject = (Expression) values.getValue(((Variable) arrayVariable).getName());
    } else arrayObject = arrayVariable;
    ArrayExpression arrayExpression = null;
    if (!(arrayObject instanceof Variable)) {
      arrayExpression =
          arrayObject instanceof ArrayExpression
              ? (ArrayExpression) arrayObject
              : (ArrayExpression) arrayObject.evaluateSMT(values);
    } else {
      arrayExpression = (ArrayExpression) arrayObject;
    }
    return (Expression)
        arrayExpression.getContent().get(parseObjectToExpression(index.evaluate(values)));
  }

  private Expression parseObjectToExpression(Object object) {
    if (object instanceof Expression) {
      return (Expression) object;
    } else if (object instanceof BigInteger) {
      return new Constant(BuiltinTypes.INTEGER, object);
    } else if (object instanceof Boolean) {
      return new Constant(BuiltinTypes.BOOL, object);
    } else {
      return null;
    }
  }

  @Override
  public Type getType() {
    return ((ArrayType) arrayVariable.getType()).getRange();
  }

  @Override
  public Expression<?>[] getChildren() {
    return new Expression[] {this.arrayVariable, this.index};
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append("(select " + arrayVariable.toString(flags) + " " + index.toString() + ")");
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {}

  @Override
  public Expression<?> duplicate(Expression[] newChildren) {
    assert newChildren.length == 2;
    Expression newArrayVariable = newChildren[0];
    Expression<?> newIndex = newChildren[1];
    if (newArrayVariable == arrayVariable && newIndex == index) return this;
    return new ArraySelectExpression(newArrayVariable, newIndex);
  }

  @Override
  public Object accept(ExpressionVisitor visitor, Object data) {
    return visitor.visit(this, data);
  }

  @Override
  public void collectFreeVariables(Collection variables) {
    if (arrayVariable instanceof Variable) {
      variables.add(arrayVariable);
    } else {
      arrayVariable.collectFreeVariables(variables);
    }
    this.index.collectFreeVariables(variables);
  }
}
