/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2023 The jConstraints Authors
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

package gov.nasa.jpf.constraints.types;

import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import java.math.BigInteger;

public class BitLimitedBVIntegerType extends ConcreteBVIntegerType<BigInteger> {

  private final BigInteger minValue;
  private final BigInteger maxValue;

  public BitLimitedBVIntegerType(int numBits, boolean signed) {
    super(
        "bitvector",
        BigInteger.class,
        BigInteger.ZERO,
        numBits,
        signed,
        signed ? BigInteger.valueOf(2).pow(numBits - 1).negate() : BigInteger.ZERO,
        BigInteger.valueOf(2).pow(numBits - (signed ? 1 : 0)).subtract(BigInteger.ONE),
        BuiltinTypes.INTEGER,
        new String[] {"bitvector"},
        BigInteger.class);
    minValue = signed ? BigInteger.valueOf(2).pow(numBits - 1).negate() : BigInteger.ZERO;
    maxValue = BigInteger.valueOf(2).pow(numBits - (signed ? 1 : 0)).subtract(BigInteger.ONE);
  }

  @Override
  public BigInteger plus(BigInteger left, BigInteger right) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger shiftLeft(BigInteger value, BigInteger shiftAmt) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger shiftRight(BigInteger value, BigInteger shiftAmt) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger shiftRightUnsigned(BigInteger value, BigInteger shiftAmt) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger not(BigInteger value) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger and(BigInteger left, BigInteger right) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger or(BigInteger left, BigInteger right) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger xor(BigInteger left, BigInteger right) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger integerValue(BigInteger value) {
    throw new UnsupportedOperationException();
  }

  @Override
  public int compare(BigInteger left, BigInteger right) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger minus(BigInteger left, BigInteger right) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger mul(BigInteger left, BigInteger right) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger div(BigInteger left, BigInteger right) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger rem(BigInteger left, BigInteger right) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger mod(BigInteger left, BigInteger right) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger negate(BigInteger num) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger cast(Object other) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BigInteger parse(String string) throws ImpreciseRepresentationException {
    BigInteger bigInt = new BigInteger(string);
    if (bigInt.bitLength() <= this.getNumBits()) {
      return bigInt;
    } else {
      throw new ArithmeticException("BigInteger out of specified bitrange");
    }
  }
}
