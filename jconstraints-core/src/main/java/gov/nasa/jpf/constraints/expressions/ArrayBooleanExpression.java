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

import java.io.IOException;
import java.util.Collection;

public class ArrayBooleanExpression extends AbstractBoolExpression {

    private final Expression<?> left;
    private final ArrayComparator comparator;
    private final Expression<?> right;

    public static ArrayBooleanExpression create(Expression<?> left,
                                                ArrayComparator operator,
                                                Expression<?> right) {
        return new ArrayBooleanExpression(left, operator, right);
    }

    public ArrayBooleanExpression(Expression<?> left,
                                  ArrayComparator comparator,
                                  Expression<?> right) {
        assert left != null && right != null &&
               left.getType() instanceof ArrayType && right.getType() instanceof ArrayType;
        this.left = left;
        this.comparator = comparator;
        this.right = right;
    }

    public Expression<?> getLeft() {
        return left;
    }

    public ArrayComparator getComparator() {
        return comparator;
    }

    public Expression<?> getRight() {
        return right;
    }

    @Override
    public Boolean evaluate(Valuation values) {
        Object lv = left.evaluate(values);
        while (lv.getClass().isAssignableFrom(ArrayStoreExpression.class)) {
            lv = ((ArrayStoreExpression) lv).evaluate(values);
        }
        Object rv = right.evaluate(values);
        while (rv.getClass().isAssignableFrom(ArrayStoreExpression.class)) {
            rv = ((ArrayStoreExpression) rv).evaluate(values);
        }
        return comparator.eval((ArrayExpression) lv, (ArrayExpression) rv);
    }

    @Override
    public Boolean evaluateSMT(Valuation values) {
        Object lv = left.evaluate(values);
        while (lv.getClass().isAssignableFrom(ArrayStoreExpression.class)) {
            lv = ((ArrayStoreExpression) lv).evaluate(values);
        }
        Object rv = right.evaluate(values);
        while (rv.getClass().isAssignableFrom(ArrayStoreExpression.class)) {
            rv = ((ArrayStoreExpression) rv).evaluate(values);
        }
        return comparator.eval((ArrayExpression) lv, (ArrayExpression) rv);
    }

    @Override
    public void collectFreeVariables(Collection<? super Variable<?>> variables) {
        if (left instanceof Variable) variables.add((Variable<?>) left);
        else this.left.collectFreeVariables(variables);
        if (right instanceof Variable) variables.add((Variable<?>) right);
        else this.right.collectFreeVariables(variables);
    }

    @Override
    public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
        return visitor.visit(this, data);
    }

    @Override
    public Expression<?>[] getChildren() {
        return new Expression[]{this.left, this.right};
    }

    @Override
    public Expression<?> duplicate(Expression<?>[] newChildren) {
        assert newChildren.length == 2;
        Expression<?> newLeft = newChildren[0], newRight = newChildren[1];
        if (left == newLeft && right == newRight) return this;
        return new ArrayBooleanExpression(newLeft, comparator, newRight);
    }

    @Override
    public void print(Appendable a, int flags) throws IOException {
        a.append('(');
        left.print(a, flags);
        a.append(' ').append(comparator.toString()).append(' ');
        right.print(a, flags);
        a.append(')');
    }

    @Override
    public void printMalformedExpression(Appendable a, int flags) throws IOException {

    }
}
