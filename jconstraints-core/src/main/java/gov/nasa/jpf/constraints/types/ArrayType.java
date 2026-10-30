/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2026 The jConstraints Authors
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

import gov.nasa.jpf.constraints.casts.CastOperation;
import java.util.Objects;

/**
 * The SMT sort {@code (Array I E)} of arrays with indices of type I and elements of type E. Arrays are symbolic
 * only: they have no Java values (models do not contain them).
 */
public class ArrayType implements Type<Object> {

  private final Type<?> indexType;
  private final Type<?> elementType;

  public ArrayType(Type<?> indexType, Type<?> elementType) {
    this.indexType = indexType;
    this.elementType = elementType;
  }

  public Type<?> getIndexType() {
    return indexType;
  }

  public Type<?> getElementType() {
    return elementType;
  }

  @Override
  public String getName() {
    return "(Array " + sortName(indexType) + " " + sortName(elementType) + ")";
  }

  private static String sortName(Type<?> t) {
    if (t instanceof BVIntegerType) {
      return "(_ BitVec " + ((BVIntegerType<?>) t).getNumBits() + ")";
    }
    if (t instanceof ArrayType) {
      return t.getName();
    }
    if (t.equals(BuiltinTypes.INTEGER)) {
      return "Int";
    }
    if (t.equals(BuiltinTypes.BOOL)) {
      return "Bool";
    }
    if (t.equals(BuiltinTypes.STRING)) {
      return "String";
    }
    return t.getName();
  }

  @Override
  public String[] getOtherNames() {
    return new String[0];
  }

  @Override
  public Class<Object> getCanonicalClass() {
    return Object.class;
  }

  @Override
  public Class<?>[] getOtherClasses() {
    return new Class[0];
  }

  @Override
  public Object cast(Object other) {
    throw new UnsupportedOperationException("arrays have no values");
  }

  @Override
  public Object getDefaultValue() {
    return null;
  }

  @Override
  public Type<?> getSuperType() {
    return null;
  }

  @Override
  public <O> CastOperation<? super O, ? extends Object> cast(Type<O> fromType) {
    return null;
  }

  @Override
  public <O> CastOperation<? super O, ? extends Object> requireCast(Type<O> fromType) {
    throw new UnsupportedOperationException("arrays cannot be cast");
  }

  @Override
  public Object parse(String string) {
    throw new UnsupportedOperationException("arrays have no values");
  }

  @Override
  public boolean equals(Type other) {
    return equals((Object) other);
  }

  @Override
  public boolean equals(Object o) {
    if (!(o instanceof ArrayType)) {
      return false;
    }
    ArrayType a = (ArrayType) o;
    return sameType(indexType, a.indexType) && sameType(elementType, a.elementType);
  }

  private static boolean sameType(Type<?> a, Type<?> b) {
    return a == b || (a != null && a.equals(b));
  }

  @Override
  public int hashCode() {
    return Objects.hash(getName());
  }

  @Override
  public String toString() {
    return getName();
  }
}
