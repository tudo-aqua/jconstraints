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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ModDivZeroException;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.NumericType;
import gov.nasa.jpf.constraints.types.Type;
import java.io.IOException;
import java.math.BigDecimal;
import java.util.Collection;
import org.apache.commons.math3.fraction.BigFraction;

/** comparison between numbers */
public class BitvectorBooleanExpression extends AbstractBoolExpression {

  private final Expression<?> left;
  private final BitvectorComparator operator;
  private final Expression<?> right;

  public BitvectorBooleanExpression(
      Expression<?> left, BitvectorComparator operator, Expression<?> right) {
    assert !(left != null && left.getType() instanceof BuiltinTypes.BoolType
        || right != null && right.getType() instanceof BuiltinTypes.BoolType);
    this.left = left;
    this.operator = operator;
    this.right = right;
  }

  public static BitvectorBooleanExpression create(
      Expression<?> left, BitvectorComparator operator, Expression<?> right) {
    return new BitvectorBooleanExpression(left, operator, right);
  }

  private <L, R> int compare(L lv, R rv) {
    NumericType<L> ltype = (NumericType<L>) left.getType();
    NumericType<R> rtype = (NumericType<R>) right.getType();

    if (ltype.equals(rtype)) {
      return ltype.compare(lv, (L) rv);
    }

    if (lv instanceof BigFraction && rv instanceof BigFraction) {
      BigFraction lNum = (BigFraction) lv;
      BigFraction rNum = (BigFraction) rv;
      return lNum.compareTo(rNum);
    }

    BigDecimal lNum = ltype.decimalValue(lv);
    BigDecimal rNum = rtype.decimalValue(rv);
    return lNum.compareTo(rNum);
  }

  @Override
  public Boolean evaluate(Valuation values) {
    Object lv = left.evaluate(values);
    Object rv = right.evaluate(values);
    int res = compare(lv, rv);
    return operator.eval(res);
  }

  @Override
  public Boolean evaluateSMT(Valuation values) {
    try {
      Object lv = left.evaluateSMT(values);
      Object rv = right.evaluateSMT(values);
      int res = compare(lv, rv);
      return operator.eval(res);
    } catch (ModDivZeroException e) {
      return true;
    }
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    this.left.collectFreeVariables(variables);
    this.right.collectFreeVariables(variables);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    final BitvectorBooleanExpression other = (BitvectorBooleanExpression) obj;
    if (this.operator != other.operator) return false;
    if (!this.left.equals(other.left)) return false;
    return this.right.equals(other.right);
  }

  @Override
  public int hashCode() {
    int hash = 3;
    hash = 43 * hash + this.left.hashCode();
    hash = 43 * hash + this.operator.hashCode();
    hash = 43 * hash + this.right.hashCode();
    return hash;
  }

  /**
   * @return the left
   */
  public Expression<?> getLeft() {
    return this.left;
  }

  /**
   * @return the comparator
   */
  public BitvectorComparator getComparator() {
    return this.operator;
  }

  /**
   * @return the right
   */
  public Expression<?> getRight() {
    return this.right;
  }

  @Override
  public Expression<?>[] getChildren() {
    return new Expression[] {left, right};
  }

  @Override
  public Expression<Boolean> duplicate(Expression<?>[] newChildren) {
    assert newChildren.length == 2;
    Expression<?> newLeft = newChildren[0], newRight = newChildren[1];
    if (left == newLeft && right == newRight) return this;
    return new BitvectorBooleanExpression(newLeft, operator, newRight);
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append('(');
    left.print(a, flags);
    a.append(' ').append(operator.toString()).append(' ');
    right.print(a, flags);
    a.append(')');
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    a.append('(');
    if (left == null) {
      a.append("null");
    } else {
      left.printMalformedExpression(a, flags);
    }
    a.append(' ').append(operator.toString()).append(' ');
    if (right == null) {
      a.append("null");
    } else {
      right.printMalformedExpression(a, flags);
    }
    a.append(')');
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  public Type<?> getOperandType() {
    return left.getType();
  }
}
