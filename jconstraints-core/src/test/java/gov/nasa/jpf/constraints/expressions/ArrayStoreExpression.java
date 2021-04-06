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
import gov.nasa.jpf.constraints.exceptions.EvaluationException;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;

public class ArrayStoreExpression extends Expression {

    private final Expression arrayVariable;

    private final Expression argument;

    private final Expression index;

    public ArrayStoreExpression (Variable arrayVariable, Expression argument, Expression index) {
        this.arrayVariable = arrayVariable;
        this.argument = argument;
        this.index = index;
    }

    public ArrayStoreExpression (Expression array, Expression argument, Expression index) {
        this.arrayVariable = array;
        this.argument = argument;
        this.index = index;
    }

    public Expression getArrayVariable() {
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
        Expression arrayObject;
        if (arrayVariable instanceof Variable) {
            arrayObject = (Expression) values.getValue(((Variable)arrayVariable).getName());
        }
        else arrayObject = arrayVariable;
        ArrayExpression arrayExpression = null;
        if (!(arrayObject instanceof Variable)) {
            arrayExpression =  arrayObject instanceof ArrayExpression ? (ArrayExpression) arrayObject : (ArrayExpression) arrayObject.evaluate(values);
        }
        else {
            arrayExpression = (ArrayExpression) arrayObject;
        }
        if (index.getType().equals(arrayExpression.getArrayType().getDomain()) &&
            argument.getType().equals(arrayExpression.getArrayType().getRange())) {
            Expression indexExp = null;
            Expression argExp = null;
            try {
                indexExp =  parseObjectToExpression(index.evaluate(values));
                argExp = parseObjectToExpression(argument.evaluate(values));
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

    private Expression parseObjectToExpression(Object object) {
        if (object instanceof Expression) {
            return (Expression) object;
        }
        else if (object instanceof BigInteger) {
            return new Constant(BuiltinTypes.INTEGER, object);
        }
        else if (object instanceof Boolean) {
            return new Constant(BuiltinTypes.BOOL, object);
        }
        else {
            return null;
        }
    }

    @Override
    public ArrayExpression evaluateSMT(Valuation values) {
        Expression arrayObject;
        if (arrayVariable instanceof Variable) {
            arrayObject = (Expression) values.getValue(((Variable)arrayVariable).getName());
        }
        else arrayObject = arrayVariable;
        ArrayExpression arrayExpression = null;
        if (!(arrayObject instanceof Variable)) {
            arrayExpression =  arrayObject instanceof ArrayExpression ? (ArrayExpression) arrayObject : (ArrayExpression) arrayObject.evaluateSMT(values);
        }
        else {
            arrayExpression = (ArrayExpression) arrayObject;
        }
        if (index.getType().equals(arrayExpression.getArrayType().getDomain()) &&
            argument.getType().equals(arrayExpression.getArrayType().getRange())) {
            Expression indexExp = null;
            Expression argExp = null;
            try {
                indexExp =  parseObjectToExpression(index.evaluateSMT(values));
                argExp = parseObjectToExpression(argument.evaluateSMT(values));
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
        assert newChildren.length == 3;
        Expression newArrayVariable = newChildren[0];
        Expression<?> newArgument = newChildren[1], newIndex = newChildren[2];
        if (newArrayVariable == arrayVariable && newArgument == argument && newIndex == index) return this;
        return new ArrayStoreExpression(newArrayVariable, newArgument, newIndex);
    }

    @Override
    public Object accept(ExpressionVisitor visitor, Object data) {
        return visitor.visit(this, data);
    }

    @Override
    public void collectFreeVariables(Collection variables) {
        if (arrayVariable instanceof Variable) {
            variables.add(arrayVariable);
        }
        else {
            arrayVariable.collectFreeVariables(variables);
        }
        this.argument.collectFreeVariables(variables);
        this.index.collectFreeVariables(variables);
    }
}
