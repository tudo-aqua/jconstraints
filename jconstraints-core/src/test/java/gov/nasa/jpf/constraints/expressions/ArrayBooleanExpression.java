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
        Object rv = right.evaluate(values);
        return comparator.eval((ArrayExpression) lv, (ArrayExpression) rv);
    }

    @Override
    public Boolean evaluateSMT(Valuation values) {
        return null;
    }

    @Override
    public void collectFreeVariables(Collection<? super Variable<?>> variables) {

    }

    @Override
    public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
        return visitor.visit(this, data);
    }

    @Override
    public Expression<?>[] getChildren() {
        return new Expression[0];
    }

    @Override
    public Expression<?> duplicate(Expression<?>[] newChildren) {
        return null;
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
