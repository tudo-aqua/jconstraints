package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.types.ArrayType;
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.math.BigInteger;
import java.util.Collection;

public class ArrayStoreExpression extends Expression {

    public ArrayExpression store(ArrayExpression arrayExpression, Expression[] arguments, Expression index) {
        Expression[] content = arrayExpression.getContent();
        ArrayType arrayType = arrayExpression.getArrayType();
        //TODO: Typecheck and extendability of array, as well as saving multiple values into array
        return new ArrayExpression(content, arrayType);
    }

    public ArrayExpression store(ArrayExpression arrayExpression, Expression argument, Expression index) {
        Expression[] content = arrayExpression.getContent();
        ArrayType arrayType = arrayExpression.getArrayType();
        //TODO: Typecheck! As well as right conversion - for right now index is assumed as an constant
        //How to resolve variables? -- "reserving" until valuation?
        //Is there a more memory efficient way? Copying does not seem like an good idea in general
        int integerIndex = ((BigInteger) ((Constant) index).getValue()).intValue();
        Expression[] destContent = new Expression[Integer.max(content.length - 1, integerIndex+1)];
        System.arraycopy(content, 0, destContent, 0, Integer.max(content.length-1, 0));
        destContent[((BigInteger) ((Constant) index).getValue()).intValue()] = argument;
        return new ArrayExpression(destContent, arrayType);
    }

    @Override
    public Object evaluate(Valuation values) {
        return null;
    }

    @Override
    public Object evaluateSMT(Valuation values) {
        return null;
    }

    @Override
    public Type getType() {
        return null;
    }

    @Override
    public Expression<?>[] getChildren() {
        return new Expression[0];
    }

    @Override
    public void print(Appendable a, int flags) throws IOException {

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
        return null;
    }

    @Override
    public void collectFreeVariables(Collection variables) {

    }
}
