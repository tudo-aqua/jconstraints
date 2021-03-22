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

import gov.nasa.jpf.constraints.api.*;
import gov.nasa.jpf.constraints.exceptions.EvaluationException;
import gov.nasa.jpf.constraints.types.ArrayType;
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;

public class ArrayStoreExpression extends Expression {

    private final Variable arrayVariable;

    private final Expression argument;

    private final Expression index;

    public ArrayStoreExpression (Variable arrayVariable, Expression argument, Expression index) {
        this.arrayVariable = arrayVariable;
        this.argument = argument;
        this.index = index;
    }

    public Variable getArrayVariable() {
        return arrayVariable;
    }

    public Expression getArgument() {
        return argument;
    }

    public Expression getIndex() {
        return index;
    }

    @Override
    public ArrayExpression evaluate(Valuation values) {
        Object objectValue = values.getValue(arrayVariable.getName());
        ArrayExpression arrayExpression = null;
        if (objectValue instanceof ArrayStoreExpression) {
            ArrayStoreExpression arrayStoreExpression = (ArrayStoreExpression) objectValue;
            arrayExpression = new ArrayExpression((ArrayType) arrayStoreExpression.arrayVariable.getType());
        }
        else if (objectValue == null) {
            //There is no array with that variable. Initializing one
            arrayExpression = new ArrayExpression((ArrayType) arrayVariable.getType());
        }
        else {
            arrayExpression = (ArrayExpression) objectValue;
        }
        if (index.getType().equals(arrayExpression.getArrayType().getDomain()) &&
            argument.getType().equals(arrayExpression.getArrayType().getRange())) {
            Expression indexExp = null;
            Expression argExp = null;
            try {
                indexExp = (Expression) index.evaluate(values);
                argExp = (Expression) argument.evaluate(values);
            }
            catch (EvaluationException ee) {
                //do not handle
            }
            indexExp = indexExp != null ? indexExp : index;
            argExp = argExp != null ? argExp : argument;
            HashMap<Expression, Expression> hashMapCopy = new HashMap<>(arrayExpression.getContent());
            hashMapCopy.put(indexExp, argExp);
            return new ArrayExpression(arrayExpression.getArrayType(), hashMapCopy);
        }
        return arrayExpression;
    }

    @Override
    public ArrayExpression evaluateSMT(Valuation values) {
        Object objectValue = values.getValue(arrayVariable.getName());
        ArrayExpression arrayExpression = null;
        if (objectValue instanceof ArrayStoreExpression) {
            ArrayStoreExpression arrayStoreExpression = (ArrayStoreExpression) objectValue;
            arrayExpression = new ArrayExpression((ArrayType) arrayStoreExpression.arrayVariable.getType());
        }
        else if (objectValue == null) {
            //There is no array with that variable. Initializing one
            arrayExpression = new ArrayExpression((ArrayType) arrayVariable.getType());
        }
        else {
            arrayExpression = (ArrayExpression) objectValue;
        }
        if (index.getType().equals(arrayExpression.getArrayType().getDomain()) &&
            argument.getType().equals(arrayExpression.getArrayType().getRange())) {
            Expression indexExp = null;
            Expression argExp = null;
            try {
                indexExp = (Expression) index.evaluateSMT(values);
                argExp = (Expression) argument.evaluateSMT(values);
            }
            catch (EvaluationException ee) {
                //do not handle
            }
            indexExp = indexExp != null ? indexExp : index;
            argExp = argExp != null ? argExp : argument;
            HashMap<Expression, Expression> hashMapCopy = new HashMap<>(arrayExpression.getContent());
            hashMapCopy.put(indexExp, argExp);
            return new ArrayExpression(arrayExpression.getArrayType(), hashMapCopy);
        }
        return arrayExpression;
    }

    @Override
    public Type getType() {
        return arrayVariable.getType();
    }

    @Override
    public Expression<?>[] getChildren() {
        return new Expression[]{this.arrayVariable, this.argument, this.index};
    }

    @Override
    public void print(Appendable a, int flags) throws IOException {
        a.append("(store "+ arrayVariable.toString(flags) + " " + argument.toString() + " " + index.toString()+")");
    }

    @Override
    public void printMalformedExpression(Appendable a, int flags) throws IOException {
        print(a, flags);
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
        variables.add(arrayVariable);
        this.argument.collectFreeVariables(variables);
        this.index.collectFreeVariables(variables);
    }
}
