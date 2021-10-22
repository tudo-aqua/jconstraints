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

package tools.aqua.jconstraints.solvers.portfolio.sequential;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.StoppableSolver;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.solvers.datastructures.ExpressionStack;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

public class SequentialMultiStrategySolverContext extends SolverContext {

  private Map<String, SolverContext> solvers;
  private boolean isCVC4Enabled = true;
  private boolean isZ3CtxBroken = false;
  private boolean isCoreChecking = true;
  private ExpressionStack stack;

  public SequentialMultiStrategySolverContext(
      Map<String, SolverContext> ctxs, boolean coreChecking) {
    this.solvers = ctxs;
    this.isCoreChecking = coreChecking;
    stack = new ExpressionStack();
  }

  @Override
  public void push() {
    stack.push();
    for (SolverContext ctx : solvers.values()) {
      ctx.push();
    }
  }

  @Override
  public void pop(int i) {
    stack.pop(i);
    for (SolverContext ctx : solvers.values()) {
      ctx.pop(i);
    }
  }

  @Override
  public Result solve(Valuation valuation) {
    Expression<Boolean> expression = ExpressionUtil.and(stack.getCurrentExpression());
    StringOrFloatExpressionVisitor visitor = new StringOrFloatExpressionVisitor();
    boolean isStringOrFloatExpression = expression.accept(visitor, null);
    Result res;

    if (isCVC4Enabled && isStringOrFloatExpression) {
      SolverContext ctx = solvers.get(SequentialMultiStrategySolver.CVC4);
      UNSATCoreSolver cvc4Unsat = (UNSATCoreSolver) ctx;
      CVC4SolverThread cvc4Solve = new CVC4SolverThread(valuation, ctx);
      ExecutorService exec = new ForkJoinPool();
      Runtime.getRuntime().addShutdownHook(new Thread(() -> exec.shutdownNow()));
      try {
        Future<Result> fres = exec.submit(cvc4Solve);
        res = fres.get(60, TimeUnit.SECONDS);

      } catch (InterruptedException | ExecutionException | TimeoutException e) {
        System.out.println("CVC4 timed out");
        if (ctx instanceof StoppableSolver) {
          StoppableSolver stoppable = (StoppableSolver) ctx;
          stoppable.stopSolver();
        }
        res = Result.ERROR;
      } finally {
        exec.shutdown();
      }
      if ((res.equals(Result.DONT_KNOW) || res.equals(Result.TIMEOUT) || res.equals(Result.ERROR))
          && !isZ3CtxBroken) {
        System.out.println("Disable process solver and shutdown exec");
        isCVC4Enabled = false;
        return solve(valuation);
      }
      if (res.equals(Result.UNSAT)) {
        return checkUnsatCore(cvc4Unsat.getUnsatCore(), SequentialMultiStrategySolver.Z3);
      }
    } else {
      res = solvers.get(SequentialMultiStrategySolver.Z3).solve(valuation);
    }
    if (res.equals(Result.DONT_KNOW)) {
      return res;
    }
    if (res.equals(Result.SAT)) {
      try {
        assert (Boolean) expression.evaluateSMT(valuation);
      } catch (Exception e) {
        if (!e.getMessage().equals("Evaluation not supported for quantifiers")) {
          res = Result.DONT_KNOW;
        }
      }
    }
    if (res.equals(Result.UNSAT)) {
      UNSATCoreSolver z3UnsatCore = (UNSATCoreSolver) solvers.get(SequentialMultiStrategySolver.Z3);
      return checkUnsatCore(z3UnsatCore.getUnsatCore(), SequentialMultiStrategySolver.CVC4);
    }
    return res;
  }

  private Result checkUnsatCore(List<Expression<Boolean>> unsatCore, String solverKey) {
    if (!isCoreChecking) {
      System.out.println("Skipepd checking unsat core");
      return Result.UNSAT;
    }
    System.out.println("Checking unsat core");
    Expression<Boolean> concat = ExpressionUtil.TRUE;
    for (Expression e : unsatCore) {
      concat = ExpressionUtil.and(concat, e);
    }
    Result res2 = solvers.get(solverKey).solve(concat, null);

    if (res2.equals(Result.UNSAT)) {
      System.out.println("UNSAT Core confirmed");
      return res2;
    } else {
      System.out.println("UNSAT Core not confirmed");
      return Result.DONT_KNOW;
    }
  }

  @Override
  public void add(List<Expression<Boolean>> list) {
    stack.add(list);
    try {
      for (SolverContext ctx : solvers.values()) {
        ctx.add(list);
      }
    } catch (RuntimeException e) {
      e.printStackTrace();
      System.out.println("There was an error during add.");
      System.out.println(Arrays.toString(list.toArray()));
      isZ3CtxBroken = true;
    }
  }

  @Override
  public void dispose() {
    stack = new ExpressionStack();
    for (SolverContext ctx : solvers.values()) {
      ctx.dispose();
    }
  }

  private static class CVC4SolverThread implements Callable<Result> {

    private final Valuation val;
    private final SolverContext ctx;

    private CVC4SolverThread(Valuation val, SolverContext ctx) {
      this.val = val;
      this.ctx = ctx;
    }

    @Override
    public Result call() {
      return ctx.solve(val);
    }
  }
}
