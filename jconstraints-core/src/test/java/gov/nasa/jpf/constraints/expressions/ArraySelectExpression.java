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
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.util.Collection;

public class ArraySelectExpression extends Expression {

    private final Variable arrayVariable;

    private final Expression index;

    public ArraySelectExpression(Variable arrayVariable, Expression index) {
        this.arrayVariable = arrayVariable;
        this.index = index;
        //TODO: Do not check for types
        //return arrayExpression.getContent()[((BigInteger)((Constant) arg).getValue()).intValue()];
    }

    public Variable getArrayVariable() {
        return arrayVariable;
    }

    public Expression getIndex() {
        return index;
    }

    @Override
    public Expression evaluate(Valuation values) {
        Object arrayObject = values.getValue(arrayVariable.getName());
        ArrayExpression arrayExpression = null;
        if (arrayObject instanceof ArrayStoreExpression) {
            arrayExpression = ((ArrayStoreExpression) arrayObject).evaluate(values);
        }
        else {
            arrayExpression = (ArrayExpression) arrayObject;
        }
        return arrayExpression.getContent().get(index);
    }

    @Override
    public Expression evaluateSMT(Valuation values) {
        Object arrayObject = values.getValue(arrayVariable.getName());
        ArrayExpression arrayExpression = null;
        if (arrayObject instanceof ArrayStoreExpression) {
            arrayExpression = ((ArrayStoreExpression) arrayObject).evaluateSMT(values);
        }
        else {
            arrayExpression = (ArrayExpression) arrayObject;
        }
        return arrayExpression.getContent().get(index);
    }

    @Override
    public Type getType() {
        return ((ArrayType)arrayVariable.getType()).getRange();
    }

    @Override
    public Expression<?>[] getChildren() {
        return new Expression[0];
    }

    @Override
    public void print(Appendable a, int flags) throws IOException {
        a.append("(select "+ arrayVariable.toString(flags) + " " + index.toString()+")");
    }

    @Override
    public void printMalformedExpression(Appendable a, int flags) throws IOException {

    }

    @Override
    public Expression<?> duplicate(Expression[] newChildren) {
        return null;
    }

    @Override
    public Object accept(ExpressionVisitor visitor, Object data) {
        return visitor.visit(this, data);
    }

    @Override
    public void collectFreeVariables(Collection variables) {

    }
}
