package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("expressions")
public class NumericBooleanExpressionTest {

  @Test
  public void createBooleanExpressionTest() {
    Constant<Boolean> f = new Constant(BuiltinTypes.BOOL, false);
    Variable<Boolean> var = Variable.create(BuiltinTypes.BOOL, "x");
    NumericBooleanExpression nbe = NumericBooleanExpression.create(var, NumericComparator.EQ, f);
  }
}
