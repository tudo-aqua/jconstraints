package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.types.Type;

public abstract class AbstractRegExExpression extends
	AbstractExpression<String>{

	@Override
	public Type<String> getType() {
		return null;
	}
}