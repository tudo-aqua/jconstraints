package io.github.tudoaqua.jconstraints.cvc5.expressions;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import io.github.tudoaqua.jconstraints.cvc5.AbstractCVC5Test;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class BitvectorTest extends AbstractCVC5Test {

    @Test
    public void testBitvectorAbs() throws IOException {
        Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
        Constant<Integer> c4 = Constant.create(BuiltinTypes.SINT32, -5);

        Expression expr = NumericBooleanExpression.create(x, NumericComparator.EQ, c4);

        Valuation val = new Valuation();
        ConstraintSolver.Result res = cvc5.solve(expr, val);
        assertEquals(res, ConstraintSolver.Result.SAT);
        assertTrue((boolean) expr.evaluate(val));

        System.out.println(val);

        Expression expr2 = BitvectorExpression.create(x, BitvectorOperator.SHIFTR, Constant.create(BuiltinTypes.SINT32, 31));
        Expression expr3 = NumericCompound.create(expr2, NumericOperator.PLUS, x);
        Expression expr4 = BitvectorExpression.create(expr3, BitvectorOperator.OR, expr2);
        Expression expr5 = NumericBooleanExpression.create(expr4, NumericComparator.EQ, Constant.create(BuiltinTypes.SINT32, 5));
        expr5.print(System.out);
        System.out.println();

        val = new Valuation();
        res = cvc5.solve(expr5, val);
        System.out.println(val);
        assertEquals(res, ConstraintSolver.Result.SAT);
        //assertTrue((boolean) expr5.evaluate(val));
    }
}
