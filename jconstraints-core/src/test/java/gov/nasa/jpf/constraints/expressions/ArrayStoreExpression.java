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
    public Object evaluateSMT(Valuation values) {
        return null;
    }

    @Override
    public Type getType() {
        return arrayVariable.getType();
    }

    @Override
    public Expression<?>[] getChildren() {
        return new Expression[0];
    }

    @Override
    public void print(Appendable a, int flags) throws IOException {
        a.append("(store "+ arrayVariable.toString(flags) + " " + argument.toString() + " " + index.toString()+")");
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
