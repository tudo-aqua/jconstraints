package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.ExpressionOperator;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import org.smtlib.CharSequenceReader;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.command.C_assert;
import org.smtlib.command.C_check_sat;
import org.smtlib.command.C_declare_fun;
import org.smtlib.command.C_exit;
import org.smtlib.command.C_set_info;
import org.smtlib.command.C_set_logic;
import org.smtlib.impl.SMTExpr.FcnExpr;
import org.smtlib.impl.SMTExpr.Let;
import org.smtlib.impl.Sort;

import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

public class SMTLIBParser {

    private static class Tuple<L, R> {
        protected L left;
        protected R right;

        private Tuple(final L left, final R right) {
            this.left = left;
            this.right = right;
        }
    }

    public SMTProblem problem;

    private final Set<Variable> letContext;

    public SMTLIBParser() {
        problem = new SMTProblem();
        letContext = new HashSet<>();
    }

    public static SMTProblem parseSMTProgram(final String input) throws
            IOException,
            IParser.ParserException,
            SMTLIBParserException {
        final SMT smt = new SMT();

        final ISource toBeParsed = smt.smtConfig.smtFactory.createSource(new CharSequenceReader(new StringReader(input),
                                                                                                input.length(),
                                                                                                100,
                                                                                                2), null);
        final IParser parser = smt.smtConfig.smtFactory.createParser(smt.smtConfig, toBeParsed);
        final SMTLIBParser smtParser = new SMTLIBParser();

        while (!parser.isEOD()) {
            ICommand cmd = parser.parseCommand();
            if (cmd instanceof C_declare_fun) {
                smtParser.processDeclareFun((C_declare_fun) cmd);
            } else if (cmd instanceof C_assert) {
                smtParser.processAssert((C_assert) cmd);
            } else if (cmd instanceof C_check_sat) {
                //It is okay, if check_sat is the last command in the chain, but it is just ignored.
                if (!parser.isEOD()) {
                    cmd = parser.parseCommand();
                    if (!(cmd instanceof C_exit)) {
                        throw new SMTLIBParserNotSupportedException(
                                "Check sat is only at the end of a smt problem allowed.");
                    }
                }
            } else if (cmd instanceof C_set_info || cmd instanceof C_set_logic) {
                //It is safe to ignore the info commands.
            } else {
                throw new SMTLIBParserNotSupportedException("Cannot pare the following command: " + cmd);
            }
        }
        return smtParser.problem;
    }

    public Expression processAssert(final C_assert cmd) throws SMTLIBParserException {
        final Expression res = processExpression(cmd.expr());
        problem.addAssertion(res);
        return res;
    }

    public void processDeclareFun(final C_declare_fun cmd) throws SMTLIBParserException {
        if (cmd.argSorts().size() != 0) {
            throw new SMTLIBParserNotSupportedException(
                    "Cannot convert the declared function, because argument size is not null. Might be implemented in" +
                    " the future.");
        }
        if (!(cmd.resultSort() instanceof Sort.Application)) {
            throw new SMTLIBParserException("Could only convert type of type Sort.Application");
        }
        final Sort.Application application = (Sort.Application) cmd.resultSort();
        final Type type = TypeMap.getType(application.toString());
        if (type == null) {
            throw new SMTLIBParserExceptionInvalidMethodCall(
                    "Could not resolve type declared in function: " + application.toString());
        }
        final Variable var = Variable.create(type, cmd.symbol().toString());
        problem.addVariable(var);
    }

    private <E> Expression<E> processArgument(final IExpr arg) throws SMTLIBParserException {
        Expression<E> resolved = null;
        if (arg instanceof ISymbol) {
            resolved = resolveSymbol((ISymbol) arg);
        } else if (arg instanceof INumeral) {
            resolved = resolveNumeral((INumeral) arg);
        } else if (arg instanceof IDecimal) {
            resolved = resolveDecimal((IDecimal) arg);
        } else if (arg instanceof FcnExpr) {
            resolved = processFunctionExpression((FcnExpr) arg);
        } else if (arg instanceof Let) {
            resolved = processLetExpression((Let) arg);
        } else {
            throw new SMTLIBParserNotSupportedException("The arguments type is not supported: " + arg.getClass());
        }
        return successfulArgumentProcessing(resolved, arg);
    }

    private Expression processExpression(final IExpr expr) throws SMTLIBParserException {
        Expression res = null;
        if (expr instanceof FcnExpr) {
            res = processFunctionExpression((FcnExpr) expr);
        } else if (expr instanceof Let) {
            res = processLetExpression((Let) expr);
        } else {
            throw new SMTLIBParserNotSupportedException("Cannot pare the subexpression of type: " + expr.getClass());
        }
        return res;
    }

    private Expression processLetExpression(final Let sExpr) throws SMTLIBParserException {
        final List<Variable> parameters = new ArrayList();
        final Map<Variable, Expression> parameterValues = new HashMap<>();
        for (final IExpr.IBinding binding : sExpr.bindings()) {
            final Expression parameterValue = processExpression(binding.expr());
            final Variable parameter = Variable.create(parameterValue.getType(), binding.parameter().value());
            parameters.add(parameter);
            parameterValues.put(parameter, parameterValue);
        }
        letContext.addAll(parameters);
        final Expression mainValue = processExpression(sExpr.expr());
        letContext.removeAll(parameters);
        return LetExpression.create(parameters, parameterValues, mainValue);
    }

    private Expression processFunctionExpression(final FcnExpr sExpr) throws SMTLIBParserException {
        final String operatorStr = sExpr.head().headSymbol().value();
        final Queue<Expression> convertedArguments = new LinkedList<>();
        for (final IExpr arg : sExpr.args()) {
            final Expression jExpr = processArgument(arg);
            convertedArguments.add(jExpr);
        }

        Expression ret = null;
        if (operatorStr.equals("not")) {
            ret = createNegation(convertedArguments);
        } else {
            final ExpressionOperator operator =
                    ExpressionOperator.fromString(FunctionOperatorMap.getjConstraintOperatorName(
                    operatorStr));
            if (operator == null) {
                System.out.println("sExpr: " + sExpr);
            }
            ret = createExpression(operator, convertedArguments);
        }
        return ret;
    }

    private Negation createNegation(final Queue<Expression> arguments) throws SMTLIBParserException {
        if (arguments.size() == 1) {
            return Negation.create(arguments.poll());
        } else {
            throw new SMTLIBParserException("Cannot use more than one Argument in a Negation Expr");
        }
    }

    private Expression createExpression(final ExpressionOperator operator, final Queue<Expression> arguments) throws
            SMTLIBParserNotSupportedException,
            SMTLIBParserExceptionInvalidMethodCall {

        checkOperatorNotNull(operator);
        checkImpliesOperatorRequirements(operator, arguments);

        Expression expr = arguments.poll();
        if (arguments.peek() == null) {
            if (operator == NumericOperator.MINUS && expr != null) {
                expr = UnaryMinus.create(expr);
            } else {
                arguments.add(expr);
                throw new SMTLIBParserExceptionInvalidMethodCall("It is strict required, that an operator is " +
                                                                 "passed together with at least two arguments in the " +
                                                                 "queue" + ".\n" + "This call got passed operator: " +
                                                                 operator + " arguments: " + arguments);
            }
        }
        while (arguments.peek() != null) {
            final Expression next = arguments.poll();
            Tuple<Expression, Expression> t = equalizeTypes(expr, next);
            if (operator instanceof NumericOperator) {

                if (operator.equals(NumericOperator.DIV) &&
                    (t.left instanceof Constant || t.left instanceof UnaryMinus)) {
                    t = new Tuple<>(convertTypeConstOrMinusConst(BuiltinTypes.DECIMAL, t.left), t.right);
                }

                if (operator.equals(NumericOperator.DIV) &&
                    (t.right instanceof Constant || t.right instanceof UnaryMinus)) {
                    t = new Tuple<>(t.left, convertTypeConstOrMinusConst(BuiltinTypes.DECIMAL, t.right));
                }

                expr = NumericCompound.create(t.left, (NumericOperator) operator, t.right);
            } else if (operator instanceof LogicalOperator) {
                expr = PropositionalCompound.create(t.left, (LogicalOperator) operator, t.right);
            } else if (operator instanceof BitvectorOperator) {
                expr = BitvectorExpression.create(t.left, (BitvectorOperator) operator, t.right);
            } else if (operator instanceof NumericComparator) {
                expr = NumericBooleanExpression.create(t.left, (NumericComparator) operator, t.right);
            } else {
                throw new SMTLIBParserNotSupportedException(
                        "Cannot convert the following operator class: " + operator.getClass());
            }
        }
        return expr;
    }


    private Constant resolveDecimal(final IDecimal decimal) {
        return Constant.create(BuiltinTypes.DECIMAL, decimal.value());
    }

    private <L, R> Tuple<L, R> equalizeTypes(final Expression left, final Expression right) throws
            SMTLIBParserExceptionInvalidMethodCall {
        if (left.getType() == right.getType()) {
            return new Tuple(left, right);
        } else if (left instanceof UnaryMinus && right instanceof UnaryMinus) {
            throw new SMTLIBParserExceptionInvalidMethodCall("Cannot equialize Types for two unary minus expressions");
        } else if ((left instanceof Constant ||
                    (left instanceof UnaryMinus && ((UnaryMinus) left).getNegated() instanceof Constant)) &&
                   BuiltinTypes.isBuiltinType(right.getType())) {
            final Expression constant = convertTypeConstOrMinusConst(right.getType(), left);
            return new Tuple(constant, right);
        } else if ((right instanceof Constant ||
                    right instanceof UnaryMinus && ((UnaryMinus) right).getNegated() instanceof Constant) &&
                   BuiltinTypes.isBuiltinType(left.getType())) {
            final Expression constant = convertTypeConstOrMinusConst(left.getType(), right);
            return new Tuple(left, constant);
        } else {
            throw new SMTLIBParserExceptionInvalidMethodCall(
                    "The expressions are not equal, but they are also not a constant and another BuiltIn " +
                    "expression type which might easily be type casted. left: " + left.getType() + " and right: " +
                    right.getType());
        }
    }

    private Expression convertTypeConstOrMinusConst(final Type type, final Expression expr) throws
            SMTLIBParserExceptionInvalidMethodCall {
        if (expr instanceof UnaryMinus) {
            return convertUnaryMinus(type, (UnaryMinus) expr);
        } else if (expr instanceof Constant) {
            return convertConstant(type, (Constant) expr);
        } else {
            throw new SMTLIBParserExceptionInvalidMethodCall(
                    "Expected a Constant or Unary Expression, but got" + expr.getClass());
        }
    }

    private UnaryMinus convertUnaryMinus(final Type type, final UnaryMinus unary) {
        return UnaryMinus.create(convertConstant(type, (Constant) unary.getNegated()));
    }

    private Constant convertConstant(final Type type, final Constant constant) {
        return Constant.create(type, constant.getValue());
    }

    private Constant resolveNumeral(final INumeral numeral) {
        return Constant.create(BuiltinTypes.INTEGER, numeral.value());
    }

    private Variable resolveSymbol(final ISymbol symbol) throws SMTLIBParserExceptionInvalidMethodCall {
        for (final Variable var : problem.variables) {
            if (var.getName().equals(symbol.value())) {
                return var;
            }
        }
        for (final Variable parameter : letContext) {
            if (parameter.getName().equals(symbol.value())) {
                return parameter;
            }
        }
        throw new SMTLIBParserExceptionInvalidMethodCall("Cannot parse Symbol: " + symbol);
    }

    private <E> Expression<E> successfulArgumentProcessing(final Expression<E> expr, final IExpr arg) throws
            SMTLIBParserException {
        if (expr == null) {
            throw new SMTLIBParserException("Cannot process the following argument: " + arg);
        }
        return expr;
    }

    private boolean checkOperatorNotNull(final ExpressionOperator operator) throws
            SMTLIBParserExceptionInvalidMethodCall {
        if (operator == null) {
            throw new SMTLIBParserExceptionInvalidMethodCall(
                    "Operator is null. Cannot create Operator dependent Expression!");
        }
        return true;
    }

    private boolean checkImpliesOperatorRequirements(final ExpressionOperator operator,
                                                     final Queue<Expression> arguments) throws
            SMTLIBParserExceptionInvalidMethodCall {
        if (operator.equals(LogicalOperator.IMPLY)) {
            if (arguments.size() == 2) {
                return true;
            } else {
                throw new SMTLIBParserExceptionInvalidMethodCall(
                        "Implies can only work with exactly two arguments, but got: " + arguments);

            }
        }
        return false;
    }

}