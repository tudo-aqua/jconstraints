package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.ArrayType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.annotations.Test;

import java.math.BigInteger;

import static org.testng.Assert.assertTrue;

@Test
public class ArrayExpressionTest {

    @Test
    public void initArrayTest() {
        ArrayType arrayType = new ArrayType(BuiltinTypes.INTEGER, BuiltinTypes.INTEGER);
        Variable int1 = new Variable(BuiltinTypes.INTEGER, "int1");
        Variable int2 = new Variable(BuiltinTypes.INTEGER, "int2");
        Variable array1 = new Variable(arrayType, "array1");
        ArrayExpression arr1 = new ArrayExpression(arrayType);
        arr1 = new ArrayStoreExpression().store(arr1, int1,
                    new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(5)));
        Variable int3 = (Variable) new ArraySelectExpression().select(arr1, new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(5)));
        Constant con1 = new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(1));
        NumericBooleanExpression numericBooleanExpression = new NumericBooleanExpression(int3, NumericComparator.EQ, con1);
        Valuation valuation = new Valuation();
        valuation.setValue(array1, arr1);
        valuation.setValue(int1, BigInteger.ONE);
        assertTrue(numericBooleanExpression.evaluate(valuation));
    }
}
