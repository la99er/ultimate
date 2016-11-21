/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;

/**
 * {@link IRefinementStrategy} with a fixed trace checker and no proof generation.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
@SuppressWarnings("rawtypes")
public class ProoflessRefinementStrategy implements IRefinementStrategy {
	private final TraceChecker mTraceChecker;
	public ProoflessRefinementStrategy(final TraceChecker traceChecker) {
		mTraceChecker = traceChecker;
	}

	@Override
	public boolean hasNext() {
		return false;
	}
	
	@Override
	public void next() {
		throw new UnsupportedOperationException("No next combination available.");
	}
	
	@Override
	public TraceChecker getTraceChecker() {
		return mTraceChecker;
	}
	
	@Override
	public IInterpolantGenerator getInterpolantGenerator() {
		throw new UnsupportedOperationException("No interpolant generator available.");
	}

	@Override
	public NestedWordAutomaton<CodeBlock, IPredicate> getInfeasibilityProof() {
		throw new UnsupportedOperationException("No infeasibility proof available.");
	}
}
