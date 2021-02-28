package gov.nasa.jpf.constraints.types;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.casts.CastOperation;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;

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
