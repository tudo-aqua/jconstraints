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

package gov.nasa.jpf.constraints.type;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.apache.commons.math3.fraction.BigFraction;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("types")
public class RealTest {

  @Test
  public void simpleRealTest() {
    Variable<BigFraction> x = Variable.create(BuiltinTypes.REAL, "x");
    Constant<BigFraction> c2_3 = Constant.create(BuiltinTypes.REAL, BigFraction.TWO_THIRDS);
    NumericBooleanExpression expr = NumericBooleanExpression.create(x, NumericComparator.EQ, c2_3);
    Valuation valSat = new Valuation();
    valSat.setValue(x, BigFraction.TWO_THIRDS);

    Valuation valUnsat = new Valuation();
    valUnsat.setValue(x, BigFraction.FOUR_FIFTHS);

    assertTrue(expr.evaluate(valSat));
    assertFalse(expr.evaluate(valUnsat));
  }
}
