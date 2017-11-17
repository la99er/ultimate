/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.hopcroft;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.AbstractMinimizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationCheckResultStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Minimization for (weakly-hierarchical) nested word automata (NWA) based on Hopcroft's minimization for DFA.
 * <p>
 * For NWA there is no unique minimum, so "minimization" is understood in the sense of "reduction".
 * <p>
 * In a nutshell, Hopcroft's algorithm maintains a partition, initially binary, and then finds witnesses that trigger a
 * split. This implementation first applies the standard splits for to finite automata for internal and call transitions
 * and then turns to return transitions (which dominate the analysis), possibly triggering also new splits for
 * internal/call transitions. We combine two different ideas:
 * <ol>
 * <li>Cheaper, but often weaker reduction (iterative):
 * <ul>
 * <li>first construct a (possibly overapproximating) partition of the states by ignoring the history encoded in call
 * and return transitions</li>
 * <li>then check that the partition is correct; if not, split again</li>
 * <li>repeat until the second check did not find a violation</li>
 * </ul>
 * </li>
 * <li>More expensive, but often stronger reduction:
 * <ul>
 * <li>more global view in return analysis that allows "better" splits</li>
 * </ul>
 * </li>
 * </ol>
 * We can combine these two ideas in the same run to analyze big partition blocks with the cheap approach and small
 * partition blocks with the stronger approach.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeNwaHopcroft<LETTER, STATE> extends AbstractMinimizeNwa<LETTER, STATE> {
	/*
	 * Hopcroft's splitting policy allows to add only one of the two resulting blocks to the worklist. However, this is
	 * only sound for deterministic automata. This flag controls if the operand should be checked for determinism
	 * initially or not.
	 */
	private static final boolean CHECK_FOR_DETERMINISM = false;

	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	private final Partition<STATE> mPartition;
	private final Worklist<STATE> mWorklistIntCall;
	private final Worklist<STATE> mWorklistRet;
	/*
	 * true only if the automaton is deterministic
	 * This can be exploited for an efficient worklist policy, which is unsound for nondeterministic automata.
	 */
	private final boolean mIsDeterministic;

	// statistics data
	private final int mInitialPartitionSize;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public MinimizeNwaHopcroft(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, null, false, true);
	}

	/**
	 * @param services
	 *            Ultimate services.
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public MinimizeNwaHopcroft(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final PartitionBackedSetOfPairs<STATE> initialPartition, final boolean addMapOldState2newState,
			final boolean separateFinalsAndNonfinals) throws AutomataOperationCanceledException {
		super(services, stateFactory);
		mOperand = operand;
		printStartMessage();

		mIsDeterministic = CHECK_FOR_DETERMINISM ? new IsDeterministic<>(mServices, mOperand).getResult() : false;

		mWorklistIntCall = Worklist.getWorklistIntCall(mOperand.size());
		mWorklistRet = Worklist.getWorklistRet(mOperand.size());
		mPartition = new Partition<>(mOperand, initialPartition, separateFinalsAndNonfinals, mWorklistIntCall,
				!mIsDeterministic);
		mInitialPartitionSize = initialPartition == null ? 0 : initialPartition.getRelation().size();

		minimize();

		// construct result with library method
		mPartition.markInitialBlocks(mOperand.getInitialStates());
		constructResultFromPartition(mPartition, addMapOldState2newState);

		printExitMessage();
	}

	private void minimize() {
		while (true) {
			while (!mWorklistIntCall.isEmpty()) {
				markAndSplit(mWorklistIntCall, true);
			}
			if (!mWorklistRet.isEmpty()) {
				markAndSplit(mWorklistRet, false);
			} else {
				// terminate
				break;
			}
		}
	}

	private void markAndSplit(final Worklist<STATE> worklist, final boolean isIntCall) {
		final Collection<STATE> splitter = worklist.poll();
		final int splitterSize = splitter.size();
		final Incomings<LETTER, STATE> incomings = isIntCall
				? new IncomingsIntCall<>(mOperand, splitter)
				: new IncomingsRet<>(mOperand, splitter, mPartition);
		while (splitter.size() == splitterSize && incomings.hasNext()) {
			for (final STATE state : incomings.next()) {
				mPartition.mark(state);
			}
			mPartition.splitAll(splitter, incomings.hasNext(), isIntCall, worklist);
		}
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = super.getAutomataOperationStatistics();
		final int largestBlockSizeInitialPartition = mPartition.getLargestBlockSizeInitialPartition();
		if (largestBlockSizeInitialPartition != 0) {
			statistics.addKeyValuePair(StatisticsType.SIZE_MAXIMAL_INITIAL_BLOCK, largestBlockSizeInitialPartition);
			statistics.addKeyValuePair(StatisticsType.SIZE_INITIAL_PARTITION, mInitialPartitionSize);
		}
		return statistics;
	}

	@Override
	protected INestedWordAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	protected Pair<Boolean, String> checkResultHelper(final IMinimizationCheckResultStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return checkLanguageEquivalence(stateFactory);
	}
}
