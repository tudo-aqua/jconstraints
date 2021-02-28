package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.types.ArrayType;
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.util.Collection;

public class ArrayExpression extends Expression {

    private final Expression<?>[] content;

    private final ArrayType arrayType;

    public ArrayExpression(ArrayType arrayType) {
        this.arrayType = arrayType;
        this.content = new Expression[]{};
    }

    public ArrayExpression(Type domain, Type range) {
        this.arrayType = new ArrayType(domain, range);
        this.content = new Expression[]{};
    }

    public ArrayExpression(Expression<?>[] content, ArrayType arrayType) {
        this.content = content;
        this.arrayType = arrayType;
    }

    public ArrayExpression(Expression<?>[] content, Type domain, Type range) {
        this.content = content;
        this.arrayType = new ArrayType(domain, range);
    }

    public Expression<?>[] getContent() {
        return content;
    }

    public ArrayType getArrayType() {
        return arrayType;
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
        return arrayType;
    }

    @Override
    public Expression<?>[] getChildren() {
        return content;
    }

    @Override
    public void print(Appendable a, int flags) throws IOException {
        a.append('[');
        for(int i = 0; i < content.length; i++) {
            content[i].print(a, flags);
            if (i < content.length -1 ){
                a.append(", ");
            }
        }
        a.append(']');
    }

    @Override
    public void printMalformedExpression(Appendable a, int flags) throws IOException {
        a.append('[');
        for(int i = 0; i < content.length; i++) {
            if (content[i] == null) {
                a.append("null");
                if (i < content.length -1 ){
                    a.append(", ");
                }
            } else {
                content[i].printMalformedExpression(a, flags);
            }
        }
        a.append(']');
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
