package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.math.BigInteger;
import java.util.Collection;

public class ArraySelectExpression extends Expression {

    public Expression select(ArrayExpression arrayExpression, Expression arg) {
        //TODO: Do not check for types
        return arrayExpression.getContent()[((BigInteger)((Constant) arg).getValue()).intValue()];
    }

    public Expression select(ArrayExpression array, Expression[] args) {
        //TODO: Do not check for types
        return null;
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
