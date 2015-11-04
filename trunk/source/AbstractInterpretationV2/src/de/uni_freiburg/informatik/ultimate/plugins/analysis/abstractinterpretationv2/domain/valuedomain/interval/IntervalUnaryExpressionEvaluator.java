/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.interval;

import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.EvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Expression evaluator for unary expressions in the interval domain.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalUnaryExpressionEvaluator
        implements INAryEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> {

	private final static int BUFFER_MAX = 100;

	protected final Logger mLogger;

	protected IEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> mSubEvaluator;
	protected UnaryExpression.Operator mOperator;

	protected IntervalUnaryExpressionEvaluator(Logger logger) {
		mLogger = logger;
	}

	@Override
	public IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>> evaluate(
	        IAbstractState<CodeBlock, BoogieVar> currentState) {

		final IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>> subEvaluatorResult = mSubEvaluator
		        .evaluate(currentState);

		switch (mOperator) {
		case ARITHNEGATIVE:
			return new EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>(
			        subEvaluatorResult.getResult().getEvaluatedValue().negate(), currentState);
		default:
			mLogger.warn(
			        "Possible loss of precision: cannot handle operator " + mOperator + ". Returning current state.");
			return new EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>(new IntervalDomainValue(),
			        currentState);

		}
	}

	@Override
	public void addSubEvaluator(
	        IEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> evaluator) {
		assert mSubEvaluator == null;
		assert evaluator != null;

		mSubEvaluator = evaluator;
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mSubEvaluator.getVarIdentifiers();
	}

	@Override
	public boolean hasFreeOperands() {
		return mSubEvaluator == null;
	}

	@Override
	public void setOperator(Object operator) {
		assert operator != null;
		assert operator instanceof Operator;
		mOperator = (Operator) operator;
	}

	@Override
	public int getArity() {
		return 1;
	}

}
