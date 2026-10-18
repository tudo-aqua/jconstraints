package gov.nasa.jpf.constraints.expressions;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportGenContext;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportVisitor;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.ArrayType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.math.BigInteger;
import java.util.Properties;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/** The theory of arrays: select, store, constant arrays, in the parser, the export, and Z3. */
public class ArrayTheoryTest {

  private ConstraintSolver solver;

  @BeforeEach
  public void initialize() {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    solver = ConstraintSolverFactory.createSolver("z3", conf);
  }

  private ConstraintSolver.Result solve(String smt, Valuation val) throws Exception {
    SMTProblem problem = SMTLIBParser.parseSMTProgram(smt);
    return solver.solve(problem.getAllAssertionsAsConjunction(), val);
  }

  @Test
  public void selectOverStore() throws Exception {
    String decls = "(declare-fun a () (Array Int (_ BitVec 32)))\n(declare-fun i () Int)\n(declare-fun j () Int)\n";
    // a different index: the old value
    assertEquals(ConstraintSolver.Result.UNSAT, solve(decls
        + "(assert (not (= i j)))\n(assert (= (select a j) #x00000001))\n"
        + "(assert (not (= (select (store a i #x00000007) j) #x00000001)))\n", new Valuation()));
    // possibly the same index (aliasing): satisfiable, and the model has the ints but no array
    Valuation val = new Valuation();
    assertEquals(ConstraintSolver.Result.SAT, solve(decls
        + "(assert (= (select a j) #x00000001))\n"
        + "(assert (= (select (store a i #x00000007) j) #x00000007))\n", val));
    assertEquals(val.getValue("i"), val.getValue("j"));
  }

  @Test
  public void constantArray() throws Exception {
    assertEquals(ConstraintSolver.Result.UNSAT, solve("(declare-fun i () Int)\n"
        + "(assert (= (select ((as const (Array Int (_ BitVec 32))) #x00000000) i) #x00000001))\n", new Valuation()));
  }

  @Test
  public void functionsOfArrays() throws Exception {
    // the elements of an object as a function returning an array (heap model)
    assertEquals(ConstraintSolver.Result.UNSAT, solve("(declare-fun elems (Int) (Array Int (_ BitVec 16)))\n"
        + "(declare-fun o1 () Int)\n(declare-fun o2 () Int)\n"
        + "(assert (= (select (elems o1) 0) #x0005))\n(assert (= o1 o2))\n"
        + "(assert (not (= (select (elems o2) 0) #x0005)))\n", new Valuation()));
  }

  @Test
  public void apiAndExport() {
    ArrayType t = new ArrayType(BuiltinTypes.INTEGER, BuiltinTypes.SINT32);
    Variable<Object> a = Variable.create(t, "a");
    Variable<BigInteger> i = Variable.create(BuiltinTypes.INTEGER, "i");
    Expression<Integer> read = ArrayExpression.select(
        ArrayExpression.store(a, i, Constant.create(BuiltinTypes.SINT32, 3)), i);
    assertEquals(BuiltinTypes.SINT32, read.getType());
    assertEquals(ConstraintSolver.Result.UNSAT, solver.solve(ExpressionUtil.and(
        NumericBooleanExpression.create(read, NumericComparator.NE, Constant.create(BuiltinTypes.SINT32, 3))),
        new Valuation()));
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    new SMTLibExportVisitor(new SMTLibExportGenContext(new PrintStream(out))).transform(
        NumericBooleanExpression.create(read, NumericComparator.EQ, Constant.create(BuiltinTypes.SINT32, 3)));
    String smt = out.toString();
    assertTrue(smt.contains("(declare-const a (Array Int (_ BitVec 32)))"), smt);
    // the export is parsed again
    try {
      assertEquals(ConstraintSolver.Result.SAT, solve(smt, new Valuation()));
    } catch (Exception e) {
      throw new AssertionError(smt, e);
    }
    assertTrue(smt.contains("(select (store a i #x00000003) i)"), smt);
    assertEquals("(Array Int (_ BitVec 32))", t.getName());
  }

  @Test
  public void memoryVersions() throws Exception {
    // SPouT's memory of int arrays: object ids to contents, a new version per write
    String m = "(Array Int (Array Int (_ BitVec 32)))";
    String decls = "(declare-fun mem.I.0 () " + m + ")\n(declare-fun mem.I.1 () " + m + ")\n"
        + "(declare-fun o1 () Int)\n(declare-fun o2 () Int)\n(declare-fun i () (_ BitVec 32))\n"
        + "(assert (= mem.I.1 (store mem.I.0 o1 (store (select mem.I.0 o1) (bv2int i) #x00000007))))\n";
    // aliasing through equal object terms and indices: the written value
    assertEquals(ConstraintSolver.Result.UNSAT, solve(decls
        + "(assert (= o1 o2))\n(assert (= i #x00000002))\n"
        + "(assert (not (= (select (select mem.I.1 o2) 2) #x00000007)))\n", new Valuation()));
    // different objects: the initial value
    assertEquals(ConstraintSolver.Result.UNSAT, solve(decls
        + "(assert (not (= o1 o2)))\n(assert (= (select (select mem.I.0 o2) 2) #x00000001))\n"
        + "(assert (not (= (select (select mem.I.1 o2) 2) #x00000001)))\n", new Valuation()));
    // both possible: satisfiable
    assertEquals(ConstraintSolver.Result.SAT, solve(decls
        + "(assert (= (select (select mem.I.0 o2) 2) #x00000001))\n"
        + "(assert (= (select (select mem.I.1 o2) 2) #x00000007))\n", new Valuation()));
  }
}
