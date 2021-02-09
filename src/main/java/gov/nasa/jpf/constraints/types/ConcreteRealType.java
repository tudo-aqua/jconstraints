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

public abstract class ConcreteRealType<T> extends ConcreteNumericType<T> implements RealType<T> {

  public ConcreteRealType(
      String name,
      Class<T> canonicalClass,
      T defaultValue,
      boolean signed,
      BigDecimal min,
      BigDecimal max,
      Type<?> superType,
      String[] otherNames,
      Class<?>... otherClasses) {
    super(
        name, canonicalClass, defaultValue, signed, min, max, superType, otherNames, otherClasses);
  }
}
