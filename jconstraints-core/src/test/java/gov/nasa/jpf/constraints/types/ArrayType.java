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

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.casts.CastOperation;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.expressions.ArrayExpression;
import gov.nasa.jpf.constraints.expressions.ArrayStoreExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.parser.ParserUtil;
import org.antlr.runtime.RecognitionException;

//Is generic type necessary?
public class ArrayType<T> implements Type<T> {

    //like input
    private final Type domain;

    //like output
    private final Type range;

    public ArrayType(Type domain, Type range) {
        //TODO: Initiliaze other objects from concrete type
        this.domain = domain;
        this.range = range;
    }

    public T store(Expression arg) {
        return null;
    }

    public T store(Expression[] args) {
        return null;
    }

    public Type getDomain() {
        return domain;
    }

    public Type getRange() {
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
    public T cast(Object other) {
        return null;
    }

    @Override
    public T getDefaultValue() {
        return null;
    }

    @Override
    public Type<?> getSuperType() {
        return null;
    }

    @Override
    public T parse(String string) throws ImpreciseRepresentationException {
        return null;
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
