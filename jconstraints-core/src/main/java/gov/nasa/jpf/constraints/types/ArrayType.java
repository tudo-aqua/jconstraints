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

import gov.nasa.jpf.constraints.casts.CastOperation;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.expressions.ArrayExpression;

//Is generic type necessary?
public class ArrayType<D, R> implements Type<ArrayType<D, R>> {

    //like input
    private final Type<D> domain;

    //like output
    private final Type<R> range;

    public ArrayType(Type<D> domain, Type<R> range) {
        //TODO: Initiliaze other objects from concrete type
        this.domain = domain;
        this.range = range;
    }

    public Type<D> getDomain() {
        return domain;
    }

    public Type<R> getRange() {
        return range;
    }

    @Override
    public String getName() {
        return null;
    }

    @Override
    public String[] getOtherNames() {
        return new String[0];
    }

    @Override
    public Class getCanonicalClass() {
        return null;
    }

    @Override
    public Class<?>[] getOtherClasses() {
        return new Class[0];
    }

    @Override
    public ArrayType<D, R> cast(Object other) {
        return null;
    }

    @Override
    public ArrayType<D, R> getDefaultValue() {
        return null;
    }

    @Override
    public Type<?> getSuperType() {
        return null;
    }

    @Override
    public ArrayType<D, R> parseUnsafe(String string) throws ImpreciseRepresentationException {
        return null;
    }

    @Override
    public ArrayType<D, R> parse(String string) throws ImpreciseRepresentationException {
        /*try {return (T) ParserUtil.parseArray(string); }
        catch (RecognitionException re) {}*/
        return null;
        /*if (string.startsWith("(store ")) {
            parseStore(string);
        }
        else if (string.startsWith("((as const ")) {
            parseArray(string);
        }*/
    }

    @Override
    public boolean equals(Type other) {
        if (other == null) {
            return false;
        }

        if (other.getClass() != this.getClass()) {
            return false;
        }

        final ArrayType otherArray = (ArrayType) other;
        if (!this.range.equals(otherArray.getRange()) || !this.domain.equals(otherArray.getDomain())) {
            return false;
        }
        return true;
    }

    /*
    private ArrayExpression parseStore(String string) throws ImpreciseRepresentationException {
        //cut '(store ' and last ')'
        string = string.substring(7, string.length()-1);
        String[] values = string.substring(string.lastIndexOf(")") + 1).split(" ");
        return new ArrayStoreExpression((Variable) parse(string), new Constant(getDomain(), values[0]), new Constant(getRange(), values[1])).evaluate(new Valuation());
    }*/

    private ArrayExpression parseArray(String string) {
        return new ArrayExpression(this);
    }

    @Override
    public CastOperation requireCast(Type fromType) {
        return null;
    }

    @Override
    public CastOperation cast(Type fromType) {
        return null;
    }
}
