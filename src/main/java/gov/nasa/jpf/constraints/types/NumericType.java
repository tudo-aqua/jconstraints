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

package gov.nasa.jpf.constraints.types;

import java.math.BigDecimal;

public interface NumericType<T> extends Type<T> {

  public boolean isSigned();

  public int compare(T left, T right);

  public BigDecimal decimalValue(T value);

  public BigDecimal getMin();

  public BigDecimal getMax();

  public T plus(T left, T right);

  public T minus(T left, T right);

  public T mul(T left, T right);

  public T div(T left, T right);

  public T rem(T left, T right);

  public T mod(T left, T right);

  public T negate(T num);

  public String toPlainString(T value);
}
