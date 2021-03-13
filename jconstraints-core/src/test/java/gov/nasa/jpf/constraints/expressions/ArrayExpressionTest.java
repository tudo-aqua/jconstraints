package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.ValuationEntry;
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
        ArrayStoreExpression arr1s = new ArrayStoreExpression(array1, int1,
                    new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(5)));
        ArraySelectExpression select1 = new ArraySelectExpression(array1,
                new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(5)));
        Constant con1 = new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(1));
        NumericBooleanExpression numericBooleanExpression = new NumericBooleanExpression(null, NumericComparator.EQ, con1);
        Valuation valuation = new Valuation();
        valuation.addEntry(new ValuationEntry<>(array1, arr1));
        assertTrue(numericBooleanExpression.evaluate(valuation));
    }

    @Test
    public void secondTest() {
        ArrayType arrayType =  new ArrayType(BuiltinTypes.INTEGER, BuiltinTypes.INTEGER);
        Variable array1 = Variable.create(arrayType, "array1");
        Variable x1 = Variable.create(BuiltinTypes.INTEGER, "x1");
        Variable y1 = Variable.create(BuiltinTypes.INTEGER, "y1");
        ArrayStoreExpression arrayStore1 = new ArrayStoreExpression(array1, x1, y1);
        Variable array2 = Variable.create(arrayType, "array2");
        Variable x2 = Variable.create(BuiltinTypes.INTEGER, "x2");
        Variable y2 = Variable.create(BuiltinTypes.INTEGER, "y2");
        ArrayStoreExpression arrayStore2 = new ArrayStoreExpression(array2, x2, y2);
        /*ArraySelectExpression arraySelect1 = new ArraySelectExpression(array1, new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(3L)));
        ArraySelectExpression arraySelect2 = new ArraySelectExpression(array2, new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(3L)));*/
        ArraySelectExpression arraySelect1 = new ArraySelectExpression(array1, y1);
        ArraySelectExpression arraySelect2 = new ArraySelectExpression(array2, y2);

        Valuation valuation = new Valuation();
        //valuation.addEntry(new ValuationEntry<>(array1, arrayStore1));
        //valuation.addEntry(new ValuationEntry<>(array2, arrayStore2));
        /*valuation.addEntry(new ValuationEntry<>(x1, new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(2)))); //argument arr1
        valuation.addEntry(new ValuationEntry<>(x2, new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(2)))); //argument arr2
        valuation.addEntry(new ValuationEntry<>(y1, new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(3)))); //index arr1
        valuation.addEntry(new ValuationEntry<>(y2, new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(3)))); //index arr2*/
        ArrayBooleanExpression arr1 = new ArrayBooleanExpression(array1, ArrayComparator.EQ, arrayStore1);
        ArrayBooleanExpression arr2 = new ArrayBooleanExpression(array2, ArrayComparator.EQ, arrayStore2);
        //NumericBooleanExpression numBo = new NumericBooleanExpression(arraySelect1.evaluate(valuation), NumericComparator.EQ, arraySelect2.evaluate(valuation));
        assertTrue(arr1.evaluate(valuation));
        //assertTrue(numBo.evaluate(valuation));

    }
}
