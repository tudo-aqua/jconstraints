package gov.nasa.jpf.constraints.expressions;

public enum RegExOperator implements ExpressionOperator {

	INTERSECTION("intersection"),
	UNION("union"),
	CONCAT("concat"),
	KLEENESTAR("*"),
	KLEENEPLUS("+"),
	OPTIONAL("?");
	  
	private final String str;

	RegExOperator(String str) {
	    this.str = str;
	  }

	  @Override
	  public String toString() {
	    return str;
	  }
	  
	  public static RegExOperator fromString(String str){
	    switch(str){
	      case "intersection": return INTERSECTION;
	      case "union": return UNION;
	      case "concat": return CONCAT;
	      case "*": return KLEENESTAR;
	      case "+": return KLEENEPLUS;
	      case "?": return OPTIONAL;
	      default: return null;
	    }
	  }
}
