package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.BoogieAstUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.NumUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

public class OctAssumeProcessor {
	
	private final OctPostOperator mPostOp;

	public OctAssumeProcessor(OctPostOperator postOperator) {
		mPostOp = postOperator;
	}
	
	public List<OctagonDomainState> assume(Expression assumption, List<OctagonDomainState> oldStates) {
		return processBooleanOperations(assumption, false, oldStates);
	}
	
	private List<OctagonDomainState> processBooleanOperations(Expression e, boolean isNegated,
			List<OctagonDomainState> oldStates) {

		assert TypeUtil.isBoolean(e.getType());

		if (e instanceof BooleanLiteral) {
			if (((BooleanLiteral) e).getValue() ^ isNegated) {
				return oldStates; // assume true
			} else {
				return new ArrayList<>(); // assume false
			}

		} else if (e instanceof IdentifierExpression) {
			String var = ((IdentifierExpression) e).getIdentifier();
			BoolValue value = BoolValue.get(!isNegated);
			oldStates.forEach(s -> s.assumeBooleanVar(var, value));
			return oldStates;

		} else if (e instanceof UnaryExpression) {
			UnaryExpression ue = (UnaryExpression) e;

			switch (ue.getOperator()) {
			case LOGICNEG:
				return processBooleanOperations(ue.getExpr(), !isNegated, oldStates);
			case OLD:
				return oldStates; // safe over-approximation
			default:
				throw new UnsupportedOperationException("Unknown, unsupported or mistyped expression: " + e);
			}

		} else if (e instanceof BinaryExpression) {
			BinaryExpression be = (BinaryExpression) e;
			Expression left = be.getLeft();
			Expression right = be.getRight();

			switch (be.getOperator()) {
			case LOGICAND:
				return isNegated ? assumeOr(left, true, right, true, oldStates)
						: assumeAnd(left, false, right, false, oldStates);
			case LOGICOR:
				return isNegated ? assumeAnd(left, true, right, true, oldStates)
						: assumeOr(left, false, right, false, oldStates);
			case LOGICIMPLIES:
				// left => right
				return isNegated ? assumeAnd(left, false, right, true, oldStates)
						: assumeOr(left, true, right, false, oldStates);
			case LOGICIFF:
				// left <=> right
				return assumeIff(left, right, isNegated, oldStates);
			case COMPEQ:
			case COMPNEQ:
			case COMPGEQ:
			case COMPGT:
			case COMPLEQ:
			case COMPLT:
			case COMPPO:
				if (TypeUtil.isNumeric(left.getType())) {
					return processNumericRelation(be, isNegated, oldStates);
				} else if (TypeUtil.isBoolean(left.getType())) {
					return processBooleanRelation(be, isNegated, oldStates);
				} else {
					// unsupported relation (e.g. array == array)
					return oldStates; // safe over-approximation
				}
			default:
				throw new UnsupportedOperationException("Unknown, unsupported or mistyped expression: " + e);
			}

		} else if (e instanceof IfThenElseExpression) {
			IfThenElseExpression ie = (IfThenElseExpression) e;
			// isNegated refers to the then and else part of the IfThenElseExpressions -- condition is not affected
			Expression condition = ie.getCondition();
			Expression notCondition = mPostOp.getExprTransformer().logicNegCached(condition);
			Expression thenPart = ie.getThenPart();
			Expression elsePart = ie.getElsePart();
			return mPostOp.splitF(oldStates,
					stateList -> processBooleanOperations(thenPart, isNegated, assume(condition, stateList)),
					stateList -> processBooleanOperations(elsePart, isNegated, assume(notCondition, stateList)));
		} else {
			// unknown expression (ArrayAccessExpression, FunctionApplication, QuantifierExpression, ...)
			return oldStates; // safe over-approximation

		}
	}
	
	private List<OctagonDomainState> assumeAnd(Expression left, boolean negLeft, Expression right, boolean negRight,
			List<OctagonDomainState> oldStates) {
		oldStates = processBooleanOperations(left, negLeft, oldStates);
		oldStates = processBooleanOperations(right, negRight, oldStates);
		return oldStates;
	}

	private List<OctagonDomainState> assumeOr(Expression left, boolean negLeft, Expression right, boolean negRight,
			List<OctagonDomainState> oldStates) {
		return mPostOp.splitF(oldStates,
				statesBeforeOr -> processBooleanOperations(left, negLeft, statesBeforeOr),
				statesBeforeOr -> processBooleanOperations(right, negRight, statesBeforeOr));
	}

	private List<OctagonDomainState> assumeIff(Expression left, Expression right, boolean negIff,
			List<OctagonDomainState> oldStates) {

		return mPostOp.splitF(oldStates,
				statesBeforeIff -> assumeAnd(left, negIff, right, false, statesBeforeIff),
				statesBeforeIff -> assumeAnd(left, !negIff, right, true, statesBeforeIff));
	}

	private List<OctagonDomainState> processBooleanRelation(BinaryExpression be, boolean isNegated,
			List<OctagonDomainState> oldStates) {
		boolean not = false;
		switch (be.getOperator()) {
		case COMPNEQ:
			not = true;
		case COMPEQ:
			return assumeIff(be.getLeft(), be.getRight(), not ^ isNegated, oldStates);
		case COMPPO:
			return oldStates; // safe over-approximation
		default:
			throw new IllegalArgumentException("Not a relation on bools: " + be);
		}
	}
	
	private List<OctagonDomainState> processNumericRelation(BinaryExpression be, boolean isNegated,
			List<OctagonDomainState> oldStates) {
		
		// TODO build binary tree from IfExprs (or same assumption may be processed multiple times)

		// isNegated refers to the relation (==, !=, <, ...) -- inner IfThenElseExpressions are not affected
		List<Pair<List<Expression>, Expression>> paths = mPostOp.getExprTransformer().removeIfExprsCached(be);
		List<OctagonDomainState> newStates = new ArrayList<>();
		for (int i = 0; i < paths.size(); ++i) {
			Pair<List<Expression>, Expression> path = paths.get(i);
			List<OctagonDomainState> tmpOldStates = (i + 1 < paths.size()) ?
					mPostOp.deepCopy(oldStates) : oldStates; // as little copies as possible
			for (Expression assumption : path.getFirst()) {
				tmpOldStates = assume(assumption, tmpOldStates);
			}
			newStates.addAll(
					processNumericRelationWithoutIfs((BinaryExpression) path.getSecond(), isNegated, tmpOldStates));
		}
		return mPostOp.joinIfGeMaxParallelStates(newStates);
	}

	private List<OctagonDomainState> processNumericRelationWithoutIfs(BinaryExpression be, boolean isNegated,
			List<OctagonDomainState> oldStates) {

		Operator op = be.getOperator();
		if (op == BinaryExpression.Operator.COMPPO) {
			return oldStates; // safe over-approximation
		} else if (isNegated) {
			op = BoogieAstUtil.negateRelOp(op);
		}

		Expression left = be.getLeft();
		Expression right = be.getRight();
		
		AffineExpression aeLeft = mPostOp.getExprTransformer().affineExprCached(left);
		AffineExpression aeRight = mPostOp.getExprTransformer().affineExprCached(right);
		if (aeLeft == null || aeRight == null) {
			// TODO (?) project to intervals and try to deduce (assume false) or even new intervals
			return oldStates; // safe over-approximation
		}
		assert left.getType().equals(right.getType());
		boolean intRelation = TypeUtil.isNumericInt(left.getType());
		boolean strictRelInt = false;
		switch (op) {
		case COMPEQ:
			return processAffineEqZero(aeLeft.subtract(aeRight), intRelation, oldStates);
		case COMPNEQ:
			return processAffineNeZero(aeLeft.subtract(aeRight), intRelation, oldStates);
		case COMPLT:
			strictRelInt = intRelation;
		case COMPLEQ:
			return processAffineLtZero(aeLeft.subtract(aeRight), strictRelInt, oldStates);
		case COMPGT:
			strictRelInt = intRelation;
		case COMPGEQ:
			return processAffineLtZero(aeRight.subtract(aeLeft), strictRelInt, oldStates);
		default:
			throw new IllegalArgumentException("Not a relation on numbers: " + op);
		}
	}
	
	
	private List<OctagonDomainState> processAffineNeZero(AffineExpression ae, boolean intRelation,
			List<OctagonDomainState> oldStates) {
		
		if (ae.isConstant()) {
			if (ae.getConstant().signum() == 0) {
				// (assume 0 != 0) is equivalent to (assume false)
				return new ArrayList<>();
			} else {
				// (assume 0 != ±7) is equivalent to (assume true)
				return oldStates;
			}
		}

		// from now on handle (ae - c != 0) as (ae <= c) or (ae >= c) ----------------
		BigDecimal leC, geC; // (ae \in [-\inf, leC]) or (ae \in [geC, \inf])
		leC = geC = ae.getConstant().negate();
		if (intRelation) {
			// in case of integers: (ae - c != 0) as (ae <= c-1) or (ae >= c+1)
			assert NumUtil.isIntegral(leC);
			leC = leC.subtract(BigDecimal.ONE);
			geC = geC.add(BigDecimal.ONE);
		}
		ae = ae.withoutConstant();

		AffineExpression.OneVarForm ovf;
		AffineExpression.TwoVarForm tvf;
		if ((ovf = ae.getOneVarForm()) != null) {
			OctValue geOc, leOc;
			if (ovf.negVar) {
				geOc = new OctValue(leC.negate());
				leOc = new OctValue(geC.negate());
			} else {
				geOc = new OctValue(geC);
				leOc = new OctValue(leC);
			}
			return mPostOp.splitC(oldStates,
					s -> s.assumeNumericVarInterval(ovf.var, geOc, OctValue.INFINITY),  // v > c
					s -> s.assumeNumericVarInterval(ovf.var, OctValue.INFINITY, leOc)); // v < c

		} else if ((tvf = ae.getTwoVarForm()) != null) {
			OctValue leOc = new OctValue(leC);
			OctValue leOc2 = new OctValue(geC.negate()); // (ae > c) is equivalent to (-ae < -c)
			return mPostOp.splitC(oldStates,
					s -> s.assumeNumericVarRelationLeConstant(tvf.var1, tvf.negVar1, tvf.var2, tvf.negVar2, leOc),
					s -> s.assumeNumericVarRelationLeConstant(tvf.var1, !tvf.negVar1, tvf.var2, !tvf.negVar2, leOc2));
			
		} else if (mPostOp.isFallbackAssumeLpSolverEnabled()) {
			// TODO use LP-solver
			mPostOp.getLogger().warn("Fallback to lp-solver not yet implemented.");
			return oldStates; // safe over-approximation
			
		} else {
			return oldStates; // safe over-approximation

		}
	}

	private List<OctagonDomainState> processAffineEqZero(AffineExpression ae, boolean intRelation,
			List<OctagonDomainState> oldStates) {
		
		if (ae.isConstant()) {
			if (ae.getConstant().signum() != 0) {
				// (assume 0 == ±7) is equivalent  to (assume false)
				return new ArrayList<>();
			} else {
				// (assume 0 == 0) is equivalent to (assume true)
				return oldStates;
			}
			
		}

		// from now on handle (ae - c == 0) as (ae == c) ----------------
		BigDecimal c = ae.getConstant().negate();
		ae = ae.withoutConstant();

		AffineExpression.OneVarForm ovf;
		AffineExpression.TwoVarForm tvf;
		if ((ovf = ae.getOneVarForm()) != null) {
			OctValue oc = new OctValue(ovf.negVar ? c.negate() : c);
			oldStates.forEach(state -> state.assumeNumericVarInterval(ovf.var, oc, oc));
			return oldStates;

		} else if ((tvf = ae.getTwoVarForm()) != null) {
			OctValue oc = new OctValue(c);
			OctValue ocNeg = new OctValue(c.negate());
			oldStates.forEach(state -> state.assumeNumericVarRelationLeConstant(
					tvf.var1, tvf.negVar1, tvf.var2, tvf.negVar2, oc));
			oldStates.forEach(state -> state.assumeNumericVarRelationLeConstant(
					tvf.var1, !tvf.negVar1, tvf.var2, !tvf.negVar2, ocNeg));
			return oldStates;

		} else if (mPostOp.isFallbackAssumeLpSolverEnabled()) {
			// TODO use LP-solver
			mPostOp.getLogger().warn("Fallback to lp-solver not yet implemented.");
			return oldStates; // safe over-approximation
			
		} else {
			return oldStates; // safe over-approximation

		}
	}

	private List<OctagonDomainState> processAffineLtZero(AffineExpression ae, boolean strictRelInt,
			List<OctagonDomainState> oldStates) {
		
		// from now on handle (ae - c <= 0) as (ae <= c) ----------------
		BigDecimal c = ae.getConstant().negate();
		if (strictRelInt) {
			// in case of integers: (ae - c < 0) as (ae <= c - 1)"
			assert NumUtil.isIntegral(c);
			c = c.subtract(BigDecimal.ONE);
		}
		ae = ae.withoutConstant();

		AffineExpression.OneVarForm ovf;
		AffineExpression.TwoVarForm tvf;
		if (ae.isConstant()) {
			if (c.signum() < 0) {
				// (assume 0 <= -7) is equivalent  to (assume false)
				return new ArrayList<>();
			} else {
				// (assume 0 <= 7) is equivalent to (assume true)
				return oldStates;
			}

		} else if ((ovf = ae.getOneVarForm()) != null) {
			OctValue min, max;
			if (ovf.negVar) {
				// (-v <= c) is equal to (v >= -c)
				min = new OctValue(c.negate());
				max = OctValue.INFINITY;
			} else {
				min = OctValue.INFINITY;
				max = new OctValue(c);
			}
			oldStates.forEach(state -> state.assumeNumericVarInterval(ovf.var, min, max));
			return oldStates;
		
		} else if ((tvf = ae.getTwoVarForm()) != null) {
			OctValue co = new OctValue(c);
			oldStates.forEach(state -> state.assumeNumericVarRelationLeConstant(
					tvf.var1, tvf.negVar2, tvf.var2, tvf.negVar1, co));
			return oldStates;
		
		} else if (mPostOp.isFallbackAssumeLpSolverEnabled()) {
			// TODO use LP-solver
			mPostOp.getLogger().warn("Fallback to lp-solver not yet implemented.");
			return oldStates; // safe over-approximation
			
		} else {
			return oldStates; // safe over-approximation

		}
	}

}
