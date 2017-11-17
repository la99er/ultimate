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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;

public abstract class Incomings<LETTER, STATE> implements Iterator<Iterable<STATE>> {
	// operand (for finding incoming transitions)
	protected final INestedWordAutomaton<LETTER, STATE> mOperand;
	// next letter to visit
	protected LETTER mNextLetter;
	protected Iterator<LETTER> mNextLetters;

	// splitter states
	protected final ArrayList<STATE> mSplitter;
	// current state index
	protected int mStatesIdx;

	protected Incomings(final INestedWordAutomaton<LETTER, STATE> operand, final Collection<STATE> splitter) {
		mOperand = operand;
		mSplitter = new ArrayList<>(splitter);
		mStatesIdx = 0;
		mNextLetter = null;
		mNextLetters = null;
	}

	/**
	 * @return The visited letters.
	 */
	protected abstract Set<LETTER> getVisitedLetters();

	protected final boolean hasStatesLeft() {
		return mStatesIdx < mSplitter.size();
	}

	protected final STATE getCurrentState() {
		return mSplitter.get(mStatesIdx);
	}

	protected final boolean findFreshLetter() {
		while (mNextLetters.hasNext()) {
			final LETTER letter = mNextLetters.next();
			if (!getVisitedLetters().contains(letter)) {
				mNextLetter = letter;
				return true;
			}
		}
		return false;
	}

	protected final void tryNextState() {
		mNextLetters = null;
		++mStatesIdx;
	}
}
