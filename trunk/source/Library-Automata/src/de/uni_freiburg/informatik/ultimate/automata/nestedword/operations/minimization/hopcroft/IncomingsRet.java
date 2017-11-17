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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeSevpa.EquivalenceClass;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;

public class IncomingsRet<LETTER, STATE> extends Incomings<LETTER, STATE> {
	private enum ReturnSplitMode {
		/**
		 * Old MinimizeSevpa behavior. TODO describe
		 */
		LAZY,
		/**
		 * Old ShrinkNwa behavior. TODO describe
		 */
		EAGER,
		/**
		 * Mixed behavior. TODO describe
		 */
		MIXED
	}

	private final Partition<STATE> mPartition;
	private final Set<LETTER> mVisitedLetters;
	// maps block of hierarchical predecessors to set of linear predecessors
	private final HashMap<Partition<STATE>.Block, HashSet<STATE>> mBlock2linSet;
	// maps block of linear predecessors to set of hierarchical predecessors
	private final HashMap<Partition<STATE>.Block, HashSet<STATE>> mBlock2hierSet;
	private ReturnSplitMode mMode;

	public IncomingsRet(final INestedWordAutomaton<LETTER, STATE> operand, final Collection<STATE> splitter,
			final Partition<STATE> partition) {
		this(operand, splitter, partition, ReturnSplitMode.LAZY);
	}

	public IncomingsRet(final INestedWordAutomaton<LETTER, STATE> operand, final Collection<STATE> splitter,
			final Partition<STATE> partition, final ReturnSplitMode mode) {
		super(operand, splitter);
		mPartition = partition;
		mMode = mode;
		mVisitedLetters = new HashSet<>();
		mBlock2linSet = new HashMap<>();
		mBlock2hierSet = new HashMap<>();
	}

	private boolean hasNextLetter() {
		if (mNextLetter != null) {
			// can only happen if this method was called twice without calling next()
			return true;
		}
		while (hasStatesLeft()) {
			// check if there is a next return letter
			if (mNextLetters == null) {
				mNextLetters = mOperand.lettersReturnIncoming(getCurrentState()).iterator();
			}
			if (findFreshLetter()) {
				return true;
			}
			tryNextState();
		}
		return false;
	}

	@Override
	public boolean hasNext() {
		while (mBlock2linSet.isEmpty() && mBlock2hierSet.isEmpty()) {
			if (!hasNextLetter()) {
				return false;
			}
			assert mNextLetter != null : "This iterator relies on first calling hasNext() before calling next().";
			determineModeAndFillMaps();

			assert !getVisitedLetters().contains(mNextLetter) : "A letter was visited twice.";
			getVisitedLetters().add(mNextLetter);
			mNextLetter = null;
		}
		return true;
	}

	private void determineModeAndFillMaps() {
		for (int i = mSplitter.size() - 1; i >= mStatesIdx; --i) {
			final STATE state = mSplitter.get(i);
			for (final IncomingReturnTransition<LETTER, STATE> trans : mOperand.returnPredecessors(state,
					mNextLetter)) {
				addStateToSetInBlockMap(trans.getHierPred(), mPartition.getBlock(trans.getLinPred()), mBlock2hierSet);
				addStateToSetInBlockMap(trans.getLinPred(), mPartition.getBlock(trans.getHierPred()), mBlock2linSet);
			}
		}

		switch (mMode) {
			case LAZY:
				computeLazyLin(mNextLetter);
				break;
			case EAGER:
			case MIXED:
			default:
				throw new UnsupportedOperationException("Mode " + mMode + "not supported yet.");
		}
	}

	private void computeLazyLin(final LETTER letter) {
		/*
		 * only linear predecessors with hierarchical predecessors
		 * from different equivalence classes are split
		 */
		// TODO Auto-generated method stub


		for (final STATE state : mSplitter.g)
		final Partition<STATE>.Block ec = mPartition.getEquivalenceClass(inTrans.getHierPred());
		HashSet<STATE> linSet = block2linSet.get(ec);
		if (linSet == null) {
			linSet = new HashSet<>();
			block2linSet.put(ec, linSet);
		}
		for (final IncomingReturnTransition<LETTER, STATE> inTransInner : partition.linPredIncoming(state,
				inTrans.getHierPred(), letter)) {
			linSet.add(inTransInner.getLinPred());
		}
	}

	private void addStateToSetInBlockMap(final STATE state, final Partition<STATE>.Block block,
			final HashMap<Partition<STATE>.Block, HashSet<STATE>> map) {
		HashSet<STATE> set = map.get(block);
		if (set == null) {
			set = new HashSet<>();
			map.put(block, set);
		}
		set.add(state);
	}

	@Override
	public Collection<STATE> next() {
//		final Collection<STATE> res = new ArrayList<>();
//		for (int i = mSplitter.size() - 1; i >= mStatesIdx; --i) {
//			final STATE state = mSplitter.get(i);
//			for (final STATE pred : getPredecessors(state, mNextLetter)) {
//				res.add(pred);
//			}
//		}
//		return res;
	}

	@Override
	protected Set<LETTER> getVisitedLetters() {
		return mVisitedLetters;
	}
}
