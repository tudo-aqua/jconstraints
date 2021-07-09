package gov.nasa.jpf.constraints.expressions;


import com.microsoft.z3.*;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.smtlib.LoadingUtil;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import gov.nasa.jpf.constraints.types.ArrayType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.Assert;
import org.testng.annotations.Test;
import org.testng.asserts.Assertion;

import java.io.IOException;
import java.net.URISyntaxException;
import java.util.*;

import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.SAT;
import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.UNSAT;
import static org.testng.Assert.assertEquals;

@Test
public class ArrayTest {

    @Test
    public void arrayTest() {
        final NativeZ3Solver solver = new NativeZ3Solver();
        final SMTProblem problem;
        List<Assertion> assertions = new ArrayList<>();
        List<Variable> variables = new ArrayList<>();
        variables.add(new Variable(BuiltinTypes.INTEGER, "x1"));
        assertions.add(new Assertion());
        variables.add(new Variable(BuiltinTypes.INTEGER, "x2"));
        variables.add(new Variable(BuiltinTypes.INTEGER, "y1"));
        variables.add(new Variable(BuiltinTypes.INTEGER, "y2"));
        variables.add(new Variable(BuiltinTypes.INTEGER, "z1"));
        variables.add(new Variable(BuiltinTypes.INTEGER, "z2"));
        List<Function> functions = new ArrayList<>();
        //functions.add(new Function());

    }

    @Test
    public void runArrayTestFromFile() throws SMTLIBParserException, IOException, URISyntaxException {
        final SMTProblem problem =
            LoadingUtil.loadProblemFromResources("test_inputs/array_constraints.smt2");
        final NativeZ3Solver solver = new NativeZ3Solver();
        final Valuation val = new Valuation();
        final ConstraintSolver.Result res = solver.solve(problem.getAllAssertionsAsConjunction(), val);
        /*
        assertEquals(res, SAT);
        assertEquals(val.getVariables().size(), 2);
        */
    }

    @Test
    public void nativeZ3ArrayTest() {
        final Map<String, String> cfg = Collections.singletonMap("model", "true");
        Context z3Context = new Context(cfg);
        IntSort intSort = z3Context.mkIntSort();
        ArrayExpr arr1 = z3Context.mkArrayConst("array1", intSort, intSort);
        IntExpr x1 = (IntExpr) z3Context.mkConst("x1", z3Context.getIntSort());
        IntExpr y1 = (IntExpr) z3Context.mkConst("y1", z3Context.getIntSort());
        arr1 = z3Context.mkStore(arr1, x1, y1);
        ArrayExpr arr2 = z3Context.mkArrayConst("array2", intSort, intSort);
        IntExpr x2 = (IntExpr) z3Context.mkConst("x2", z3Context.getIntSort());
        IntExpr y2 = (IntExpr) z3Context.mkConst("y2", z3Context.getIntSort());
        arr2 = z3Context.mkStore(arr2, x2, y2);
        IntExpr z1 = (IntExpr) z3Context.mkSelect(arr1, z3Context.mkInt(3));
        IntExpr z2 = (IntExpr) z3Context.mkSelect(arr2, z3Context.mkInt(3));

        ArraySort intArray = z3Context.mkArraySort(intSort, intSort);
        ArrayExpr arr3 = (ArrayExpr) z3Context.mkConst("array3", intArray);
        //This equals to z3Context.mkArrayConst("array3", intSort, intSort);

        BoolExpr boolAssumption = z3Context.mkEq(z1, z2);
        Solver solver = z3Context.mkSolver();
        Status solverStatus = solver.check(boolAssumption);
        System.out.println(solver.getModel().toString());
        assertEquals(solverStatus, Status.SATISFIABLE);
    }

    @Test
    public void arrayTestJConstraints() {
        Properties conf = new Properties();
        conf.setProperty("model", "true");
        conf.setProperty("symbolic.dp", "NativeZ3");
        ConstraintSolverFactory factory = new ConstraintSolverFactory();
        ConstraintSolver solver = factory.createSolver("z3", conf);

        SolverContext ctx = solver.createContext();

        ArrayType arrayType =  new ArrayType(BuiltinTypes.INTEGER, BuiltinTypes.INTEGER);
        Variable array1 = Variable.create(arrayType, "array1");
        Variable x1 = Variable.create(BuiltinTypes.INTEGER, "x1");
        Variable y1 = Variable.create(BuiltinTypes.INTEGER, "y1");
        ArrayStoreExpression arrayStore1 = new ArrayStoreExpression(array1, x1, y1);
        Variable array2 = Variable.create(arrayType, "array2");
        Variable x2 = Variable.create(BuiltinTypes.INTEGER, "x2");
        Variable y2 = Variable.create(BuiltinTypes.INTEGER, "y2");
        ArrayStoreExpression arrayStore2 = new ArrayStoreExpression(array2, x2, y2);
        ArraySelectExpression arraySelect1 = new ArraySelectExpression(array1, y1);
        ArraySelectExpression arraySelect2 = new ArraySelectExpression(array2, y2);
        Valuation valuation = new Valuation();
        ArrayBooleanExpression abe1 = new ArrayBooleanExpression(array1, ArrayComparator.EQ, arrayStore1);
        ArrayBooleanExpression abe2 = new ArrayBooleanExpression(array2, ArrayComparator.EQ, arrayStore2);
        NumericBooleanExpression numBo = new NumericBooleanExpression(arraySelect1, NumericComparator.EQ, arraySelect2);
        PropositionalCompound pcAbe = new PropositionalCompound(abe1, LogicalOperator.AND, abe2);
        PropositionalCompound abe = new PropositionalCompound(pcAbe, LogicalOperator.AND, numBo);
        ctx.add(abe);
        ConstraintSolver.Result result = solver.solve(abe, valuation);
        Assert.assertEquals(result, SAT);
        Assert.assertTrue(numBo.evaluate(valuation));
    }

    @Test
    public void testParser() throws SMTLIBParserException, IOException, URISyntaxException {
        final SMTProblem problem =
            LoadingUtil.loadProblemFromResources("test_inputs/array_constraints.smt2");
        final NativeZ3Solver solver = new NativeZ3Solver();
        final Valuation val = new Valuation();
        final ConstraintSolver.Result res = solver.solve(problem.getAllAssertionsAsConjunction(), val);
        assertEquals(res, SAT);
    }

    @Test
    public void testPointerSafe() throws SMTLIBParserException, IOException, URISyntaxException {
        final SMTProblem problem =
            LoadingUtil.loadProblemFromResources("test_inputs/pointer-safe-5.smt2");
        final NativeZ3Solver solver = new NativeZ3Solver();
        final Valuation val = new Valuation();
        final ConstraintSolver.Result res = solver.solve(problem.getAllAssertionsAsConjunction(), val);
        assertEquals(res, UNSAT);
    }
}
