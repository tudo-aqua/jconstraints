package gov.nasa.jpf.constraints.expressions;

public enum ArrayComparator implements ExpressionOperator {
    EQ("==") {
        public ArrayComparator not() {
            return NE;
        }

        public boolean eval(ArrayExpression arr1, ArrayExpression arr2) {
            return arr1.getContent().equals(arr2.getContent());
        }
    },
    NE("!=") {
        public ArrayComparator not() {
            return EQ;
        }

        public boolean eval(ArrayExpression arr1, ArrayExpression arr2) {
            return arr1.getContent().equals(arr2.getContent());
        }
    };

    private final String str;

    private ArrayComparator(String str) {
        this.str = str;
    }

    public abstract ArrayComparator not();

    public abstract boolean eval(ArrayExpression arr1, ArrayExpression arr2);

    @Override
    public String toString() {
        return str;
    }

    public static ArrayComparator fromString(String str) {
        switch (str) {
            case "==":
                return EQ;
            case "!=":
                return NE;
            default:
                return null;
        }
    }
}
