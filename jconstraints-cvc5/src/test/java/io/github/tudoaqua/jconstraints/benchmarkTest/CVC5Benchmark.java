package io.github.tudoaqua.jconstraints.benchmarkTest;

import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import io.github.tudoaqua.jconstraints.cvc5.CVC5SolverProvider;
import java.util.Properties;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.params.ParameterizedTest;
import tools.aqua.jconstraints.benchmarktest.api.TestCaseSource;
import tools.aqua.jconstraints.benchmarktest.benchmarks.SINT32ConstantTestExpressions;
import tools.aqua.jconstraints.benchmarktest.benchmarks.SINT32VariableTestExpressions;
import tools.aqua.jconstraints.benchmarktest.benchmarks.SINT64ConstantTestExpressions;
import tools.aqua.jconstraints.benchmarktest.benchmarks.StringConstantTestExpressions;
import tools.aqua.jconstraints.benchmarktest.benchmarks.TestCase;

public class CVC5Benchmark {
  private static CVC5SolverProvider provider;
  private static ConstraintSolver solver;

  @BeforeAll
  public static void init() {
    provider = new CVC5SolverProvider();
    solver = provider.createSolver(new Properties());
  }

  @ParameterizedTest
  @TestCaseSource({
    SINT32ConstantTestExpressions.class,
    SINT64ConstantTestExpressions.class,
    SINT32VariableTestExpressions.class,
    StringConstantTestExpressions.class
  })
  public void testAll(TestCase test) {
    assertEquals(test.getExpectedResult(), solver.isSatisfiable(test.getTest()));
  }
}
