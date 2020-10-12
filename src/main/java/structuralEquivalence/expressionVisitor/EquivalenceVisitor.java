package structuralEquivalence.expressionVisitor;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorNegation;
import gov.nasa.jpf.constraints.expressions.BooleanExpression;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
import gov.nasa.jpf.constraints.expressions.RegexCompoundExpression;
import gov.nasa.jpf.constraints.expressions.RegexOperatorExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringCompoundExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;

import java.util.HashMap;
import java.util.Map;

public class EquivalenceVisitor extends AbstractExpressionVisitor<Boolean, Expression> {
	private Map<Variable, Variable> renamingMap = new HashMap<>();

	@Override
	public <E> Boolean visit(Variable<E> variable, Expression expression) {
		if (expression instanceof Variable){
			Variable var = (Variable) expression;
			if(variable.getType().equals(var.getType())){
				if (var.getName().equals(var.getName())){
					return true;
				} else if(renamingMap.containsKey(var)){
					return renamingMap.get(var).getName().equals(variable.getName());
				} else {
					renamingMap.put(var, variable);
					return false;
				}
			}
		}
		return false;
	}

	@Override
	public <E> Boolean visit(Constant<E> constant, Expression expression) {
		if(expression instanceof Constant) {
			Constant constantRight = (Constant) expression;
			return constant.getType().equals(expression.getType()) && constantRight.getValue().equals(constant.getValue());
		}
		return false;
	}

	@Override
	public Boolean visit(Negation negation, Expression expression) {
		if(expression instanceof Negation){
			Negation right = (Negation) expression;
			return visit(negation.getNegated(), right.getNegated());
		}
		return false;
	}

	@Override
	public Boolean visit(NumericBooleanExpression numericBooleanExpression, Expression expression) {
		if (expression instanceof NumericBooleanExpression){
			NumericBooleanExpression right = (NumericBooleanExpression) expression;
			boolean leftChecked = visit(numericBooleanExpression.getLeft(), right.getLeft());
			boolean rightChecked = visit(numericBooleanExpression.getRight(), right.getRight());
			return leftChecked && rightChecked && numericBooleanExpression.getComparator().equals(right.getComparator());
		}
		return false;
	}

	@Override
	public Boolean visit(RegExBooleanExpression regExBooleanExpression, Expression expression) {
		if(expression instanceof RegExBooleanExpression){
			RegExBooleanExpression right = (RegExBooleanExpression) expression;
			boolean leftChecked = visit(regExBooleanExpression.getLeft(), right.getLeft());
			boolean rightChecked = visit(regExBooleanExpression.getRight(), right.getRight());
			return  leftChecked && rightChecked;
		}
		return false;
	}

	@Override
	public Boolean visit(StringBooleanExpression stringBooleanExpression, Expression expression) {
		if(expression instanceof StringBooleanExpression){
			StringBooleanExpression right = (StringBooleanExpression) expression;
			boolean leftChecked = visit(stringBooleanExpression.getLeft(), right.getLeft());
			boolean rightChecked = visit(stringBooleanExpression.getRight(), right.getRight());
			return leftChecked && rightChecked && stringBooleanExpression.getOperator().equals(right.getOperator());
		}
		return false;
	}

	@Override
	public Boolean visit(StringIntegerExpression stringIntegerExpression, Expression expression) {
		if(expression instanceof StringIntegerExpression){
			StringIntegerExpression right = (StringIntegerExpression) expression;
			boolean leftChecked = visit(stringIntegerExpression.getLeft(), right.getLeft());
			boolean rightChecked = stringIntegerExpression.getRight() != null? visit(stringIntegerExpression.getRight(), right.getRight()): right.getRight() == null;
			boolean offsetChecked = stringIntegerExpression.getOffset() != null? visit(stringIntegerExpression.getOffset(), right.getOffset()): right.getOffset() == null;
			boolean operatorChecked = stringIntegerExpression.getOperator().equals(right.getOperator());
			return leftChecked && rightChecked && offsetChecked && operatorChecked;
		}
		return false;
	}

	@Override
	public Boolean visit(StringCompoundExpression stringCompoundExpression, Expression expression) {
		if(expression instanceof StringCompoundExpression){
			StringCompoundExpression right = (StringCompoundExpression) expression;
			if(stringCompoundExpression.getOperator().equals(right.getOperator())){
				switch (stringCompoundExpression.getOperator()){
					case AT:
						return checkAtString(stringCompoundExpression, right);
					case TOSTR:
						return checkToString(stringCompoundExpression, right);
					case CONCAT:
						return checkConcat(stringCompoundExpression, right);
					case SUBSTR:
						return checkSubstr(stringCompoundExpression, right);
					case REPLACE:
						return checkReplace(stringCompoundExpression, right);
				}
			}
		}
		return false;
	}

	private boolean checkAtString(StringCompoundExpression left, StringCompoundExpression right){
		boolean mainChecked = visit(left.getMain(), right.getMain());
		boolean positionChecked = visit(left.getPosition(), right.getPosition());
		boolean expressionsNull = left.getExpressions() == null && right.getExpressions() == null;
		boolean offsetNull = left.getOffset() == null && right.getOffset() == null;
		boolean lengthNull = left.getLength() == null && right.getLength() == null;
		boolean srcNull = left.getSrc() == null && right.getSrc() == null;
		boolean dstNull = left.getDst() == null && right.getDst() == null;
		return mainChecked && positionChecked && expressionsNull && offsetNull && lengthNull && srcNull && dstNull;
	}

	private boolean checkToString(StringCompoundExpression left, StringCompoundExpression right){
		boolean mainChecked = visit(left.getMain(), right.getMain());
		boolean positionNull = left.getPosition() == null && right.getPosition() == null;
		boolean expressionsNull = left.getExpressions() == null && right.getExpressions() == null;
		boolean offsetNull = left.getOffset() == null && right.getOffset() == null;
		boolean lengthNull = left.getLength() == null && right.getLength() == null;
		boolean srcNull = left.getSrc() == null && right.getSrc() == null;
		boolean dstNull = left.getDst() == null && right.getDst() == null;
		return mainChecked && positionNull && expressionsNull && offsetNull && lengthNull && srcNull && dstNull;
	}

	private boolean checkConcat(StringCompoundExpression left, StringCompoundExpression right){
		boolean mainNull = left.getMain() == null && right.getMain() == null;
		boolean positionNull = left.getPosition() == null && right.getPosition() == null;
		boolean offsetNull = left.getOffset() == null && right.getOffset() == null;
		boolean lengthNull = left.getLength() == null && right.getLength() == null;
		boolean srcNull = left.getSrc() == null && right.getSrc() == null;
		boolean dstNull = left.getDst() == null && right.getDst() == null;

		boolean expressionsChecked = right.getExpressions().length == left.getExpressions().length;

		for(int i = 0; i < left.getExpressions().length && expressionsChecked; i++){
			expressionsChecked = expressionsChecked && visit(left.getExpressions()[i], right.getExpressions()[i]);
		}

		return mainNull && positionNull && expressionsChecked && offsetNull && lengthNull && srcNull && dstNull;
	}

	private boolean checkSubstr(StringCompoundExpression left, StringCompoundExpression right){
		boolean mainChecked = visit(left.getMain(), right.getMain());
		boolean positionNull = left.getPosition() == null && right.getPosition() == null;
		boolean expressionsNull = left.getExpressions() == null && right.getExpressions() == null;
		boolean offsetChecked = visit(left.getOffset(), right.getOffset());
		boolean lengthChecked = visit(left.getLength(), right.getLength());
		boolean srcNull = left.getSrc() == null && right.getSrc() == null;
		boolean dstNull = left.getDst() == null && right.getDst() == null;
		return mainChecked && positionNull && expressionsNull && offsetChecked && lengthChecked && srcNull && dstNull;
	}

	private boolean checkReplace(StringCompoundExpression left, StringCompoundExpression right){
		boolean mainChecked = visit(left.getMain(), right.getMain());
		boolean positionNull = left.getPosition() == null && right.getPosition() == null;
		boolean expressionsNull = left.getExpressions() == null && right.getExpressions() == null;
		boolean offsetNull = left.getOffset() == null && right.getOffset() == null;
		boolean lengthNull = left.getLength() == null && right.getLength() == null;
		boolean srcChecked = visit(left.getSrc(), right.getSrc());
		boolean dstChecked = visit(left.getDst(), right.getDst());
		return mainChecked && positionNull && expressionsNull && offsetNull && lengthNull && srcChecked && dstChecked;
	}

	@Override
	public Boolean visit(RegexCompoundExpression regexCompoundExpression, Expression expression) {
		if(expression instanceof RegexCompoundExpression){
			RegexCompoundExpression right = (RegexCompoundExpression) expression;
			boolean leftChecked = visit(regexCompoundExpression.getLeft(), right.getLeft());
			boolean rightChecked = visit(regexCompoundExpression.getRight(), right.getRight());
			return  leftChecked && rightChecked && regexCompoundExpression.getOperator().equals(right.getOperator());
		}
		return false;
	}

	@Override
	public Boolean visit(RegexOperatorExpression regexOperatorExpression, Expression expression) {
		if(expression instanceof RegexOperatorExpression){
			RegexOperatorExpression right = (RegexOperatorExpression) expression;
			if(regexOperatorExpression.getOperator().equals(right.getOperator())){
				switch(regexOperatorExpression.getOperator()){
					case RANGE:
					case NOSTR:
					case ALLCHAR:
					case STRTORE:
						return checkStrToRe(regexOperatorExpression, right);
					case OPTIONAL:
					case LOOP:
					case KLEENEPLUS:
					case KLEENESTAR:
						return checkOptional(regexOperatorExpression, right);
				}
			}
		}
		return false;
	}

	private Boolean checkOptional(RegexOperatorExpression regexOperatorExpression, RegexOperatorExpression right) {
		boolean contentChecked = visit(regexOperatorExpression.getLeft(), right.getLeft());
		boolean lowChecked = regexOperatorExpression.getLow() == right.getLow();
		boolean highChecked = regexOperatorExpression.getHigh() == right.getHigh();
		boolean ch1Checked = regexOperatorExpression.getCh1() == right.getCh1();
		boolean ch2Checked = regexOperatorExpression.getCh2() == right.getCh2();
		boolean sChecked = regexOperatorExpression.getS().equals(right.getS());
		return contentChecked && lowChecked && highChecked && ch1Checked && ch2Checked && sChecked;
	}

	private Boolean checkStrToRe(RegexOperatorExpression regexOperatorExpression, RegexOperatorExpression right) {
		boolean contentNull = regexOperatorExpression.getLeft() == null && right.getLeft() == null;
		boolean lowChecked = regexOperatorExpression.getLow() == right.getLow();
		boolean highChecked = regexOperatorExpression.getHigh() == right.getHigh();
		boolean ch1Checked = regexOperatorExpression.getCh1() == right.getCh1();
		boolean ch2Checked = regexOperatorExpression.getCh2() == right.getCh2();
		boolean sChecked = regexOperatorExpression.getS().equals(right.getS());
		return contentNull && lowChecked && highChecked && ch1Checked && ch2Checked && sChecked;
	}

	@Override
	public <F, E> Boolean visit(CastExpression<F, E> castExpression, Expression expression) {
		if(expression instanceof CastExpression){
			CastExpression right = (CastExpression) expression;
			boolean fromType = castExpression.getCastOp().getFromClass().equals(right.getCastOp().getToClass());
			boolean toType = castExpression.getCastOp().getToClass().equals(right.getCastOp().getToClass());
			boolean checkCasted = visit(castExpression.getCasted(), right.getCasted());
			return fromType && toType && checkCasted;
		}
		return false;
	}

	@Override
	public <E> Boolean visit(NumericCompound<E> numericCompound, Expression expression) {
		if( expression instanceof NumericCompound){
			NumericCompound right = (NumericCompound) expression;
			boolean leftChecked = visit(numericCompound.getLeft(), right.getLeft());
			boolean rightChecked = visit(numericCompound.getRight(), right.getRight());
			boolean operator = numericCompound.getOperator().equals(right.getOperator());
			return leftChecked && rightChecked && operator;
		}
		return false;
	}

	@Override
	public Boolean visit(PropositionalCompound propositionalCompound, Expression expression) {
		if(expression instanceof PropositionalCompound){
			PropositionalCompound right = (PropositionalCompound) expression;
			boolean leftChecked = visit(propositionalCompound.getLeft(), right.getLeft());
			boolean rightChecked = visit(propositionalCompound.getRight(), right.getRight());
			boolean operator = propositionalCompound.getOperator().equals(right.getOperator());
			return leftChecked && rightChecked && operator;
		}
		return false;
	}

	@Override
	public <E> Boolean visit(IfThenElse<E> ifThenElse, Expression expression) {
		if(expression instanceof IfThenElse){
			IfThenElse right = (IfThenElse) expression;
			if(ifThenElse.getType().equals(right.getType())) {
				boolean conditionChecked = visit(ifThenElse.getIf(), right.getIf());
				boolean thenChecked = visit(ifThenElse.getThen(), right.getThen());
				boolean elseChecked = visit(ifThenElse.getElse(), right.getElse());
				return conditionChecked && thenChecked && elseChecked;
			}
		}
		return false;
	}

	@Override
	public <E> Boolean visit(UnaryMinus<E> unaryMinus, Expression expression) {
		if(expression instanceof UnaryMinus){
			UnaryMinus right = (UnaryMinus) expression;
			return visit(unaryMinus.getNegated(), right.getNegated());
		}
		return false;
	}

	@Override
	public <E> Boolean visit(BitvectorExpression<E> bitvectorExpression, Expression expression) {
		if(expression instanceof BitvectorExpression){
			BitvectorExpression right = (BitvectorExpression) expression;
			boolean leftChecked = visit(bitvectorExpression.getLeft(), right.getLeft());
			boolean rightChecked = visit(bitvectorExpression.getRight(), right.getRight());
			boolean operator = bitvectorExpression.getOperator().equals(right.getOperator());
			return leftChecked && rightChecked && operator;
		}
		return false;
	}

	@Override
	public <E> Boolean visit(BitvectorNegation<E> bitvectorNegation, Expression expression) {
		if(expression instanceof BitvectorNegation){
			BitvectorNegation right = (BitvectorNegation) expression;
			return visit(bitvectorNegation.getNegated(), right.getNegated());
		}
		return false;
	}

	@Override
	public Boolean visit(QuantifierExpression quantifierExpression, Expression expression) {
		throw new UnsupportedOperationException("We still need this for Quantifier");
	}

	@Override
	public <E> Boolean visit(FunctionExpression<E> functionExpression, Expression expression) {
		throw new UnsupportedOperationException("We still need this for FuncitonExpression");
	}

	@Override
	public Boolean visit(BooleanExpression booleanExpression, Expression expression) {
		if(expression instanceof BooleanExpression){
			BooleanExpression right = (BooleanExpression) expression;
			boolean leftChecked = visit(booleanExpression.getLeft(), right.getLeft());
			boolean rightChecked = visit(booleanExpression.getRight(), right.getRight());
			boolean operator = booleanExpression.getOperator().equals(right.getOperator());
			return leftChecked && rightChecked && operator;
		}
		return false;
	}
}
