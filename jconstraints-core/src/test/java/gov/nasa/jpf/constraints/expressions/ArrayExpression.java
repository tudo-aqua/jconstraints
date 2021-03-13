package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.types.ArrayType;
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

public class ArrayExpression extends Expression {

    private final HashMap<Expression, Expression> content;

    private final ArrayType arrayType;

    public ArrayExpression(ArrayType arrayType) {
        this.arrayType = arrayType;
        this.content = new HashMap<>();
    }

    public ArrayExpression(Type domain, Type range) {
        this.arrayType = new ArrayType(domain, range);
        this.content = new HashMap<>();
    }

    public ArrayExpression(Type domain, Type range, HashMap<Expression, Expression> content) {
        this.arrayType = new ArrayType(domain, range);
        this.content = content;
    }

    public ArrayExpression(ArrayType arrayType, HashMap<Expression, Expression> content) {
        this.arrayType = arrayType;
        this.content = content;
    }

    public HashMap<Expression, Expression> getContent() {
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
        return null;
    }

    @Override
    public void print(Appendable a, int flags) throws IOException {
        a.append('[');
        int size = content.size();
        int i = 0;
        for (Map.Entry<Expression, Expression> entry : content.entrySet()) {
            i++;
            if (entry.getKey() != null && entry.getValue() != null) {
                a.append(entry.getKey().toString() + " - " + entry.getValue().toString());
                if (i < size) {
                    a.append(", ");
                }
            }
            else if (entry.getKey() == null){
                entry.getKey().printMalformedExpression(a, flags);
            }
            else {
                entry.getValue().printMalformedExpression(a, flags);
            }
        }
        a.append(']');
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
        return null;
    }

    @Override
    public void collectFreeVariables(Collection variables) {

    }
}
