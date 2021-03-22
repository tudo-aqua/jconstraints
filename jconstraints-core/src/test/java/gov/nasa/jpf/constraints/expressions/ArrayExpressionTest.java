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
    public void arrayConstraintTest() {
        ArrayType arrayType =  new ArrayType(BuiltinTypes.INTEGER, BuiltinTypes.INTEGER);
        Variable array1 = Variable.create(arrayType, "array1");
        Variable x1 = Variable.create(BuiltinTypes.INTEGER, "x1");
        Variable y1 = Variable.create(BuiltinTypes.INTEGER, "y1");
        ArrayStoreExpression arrayStore1 = new ArrayStoreExpression(array1, x1, y1);
        Variable array2 = Variable.create(arrayType, "array2");
        Variable x2 = Variable.create(BuiltinTypes.INTEGER, "x2");
        Variable y2 = Variable.create(BuiltinTypes.INTEGER, "y2");
        ArrayStoreExpression arrayStore2 = new ArrayStoreExpression(array2, x2, y2);
        ArraySelectExpression arraySelect1 = new ArraySelectExpression(array1, y1);
        ArraySelectExpression arraySelect2 = new ArraySelectExpression(array2, y2);

        Valuation valuation = new Valuation();
        valuation.addEntry(new ValuationEntry<>(array1, arrayStore1));
        valuation.addEntry(new ValuationEntry<>(array2, arrayStore2));
        valuation.addEntry(new ValuationEntry<>(x1, BigInteger.valueOf(2))); //argument arr1
        valuation.addEntry(new ValuationEntry<>(x2,  BigInteger.valueOf(2))); //argument arr2
        /*valuation.addEntry(new ValuationEntry<>(y1, new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(3)))); //index arr1
        valuation.addEntry(new ValuationEntry<>(y2, new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(3)))); //index arr2 */
        ArrayBooleanExpression arr1 = new ArrayBooleanExpression(array1, ArrayComparator.EQ, arrayStore1);
        ArrayBooleanExpression arr2 = new ArrayBooleanExpression(array2, ArrayComparator.EQ, arrayStore2);
        NumericBooleanExpression numBo = new NumericBooleanExpression(arraySelect1.evaluate(valuation), NumericComparator.EQ, arraySelect2.evaluate(valuation));
        assertTrue(arr1.evaluate(valuation));
        assertTrue(arr2.evaluate(valuation));
        assertTrue(numBo.evaluate(valuation));
    }
}
