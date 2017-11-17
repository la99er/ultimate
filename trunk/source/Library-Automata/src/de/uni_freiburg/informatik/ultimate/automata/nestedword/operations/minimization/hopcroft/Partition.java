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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.IAutomatonStatePartition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.IBlock;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;

/**
 * Partition data structure specialized for Hopcroft-style minimization algorithms.
 * <p>
 * TODO document everything
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <STATE>
 *            state type
 */
public class Partition<STATE> implements IAutomatonStatePartition<STATE> {
	// operand (for finding initial and final states)
	private final INestedWordAutomaton<?, STATE> mOperand;
	// array of all states
	private final STATE[] mStates;
	// maps a state to its index in the states array and to its block
	private final HashMap<STATE, PosBlockPair> mState2PosAndBlock;
	// marks the index where the next state can be inserted (only necessary during initialization)
	private int mFirstInvalidIndex;
	// size of the partition (number of blocks)
	private int mSize;
	// largest block size in the initial partition
	private final int mLargestBlockSizeInitialPartition;
	// contains those blocks that are marked during refinement
	private final Deque<Block> mMarkedBlocks;
	// contains those blocks that contain an initial state in the final stage; LinkedHashSet for iteration order
	private final LinkedHashSet<Block> mInitialBlocks;
	/*
	 * true if the automaton is nondeterministic, in which case we cannot exploit the efficient worklist policy
	 * (because it is unsound for nondeterministic automata)
	 */
	private final boolean mIsNondeterministic;

	public Partition(final INestedWordAutomaton<?, STATE> operand,
			final PartitionBackedSetOfPairs<STATE> initialPartition, final boolean separateFinalsAndNonfinals,
			final Worklist<STATE> worklistIntCall, final boolean isNondeterministic) {
		mOperand = operand;
		final int numberOfStates = operand.size();
		mStates = initializeArray(numberOfStates);
		mState2PosAndBlock = new HashMap<>(numberOfStates);
		mFirstInvalidIndex = 0;
		mSize = 0;
		mMarkedBlocks = new ArrayDeque<>();
		mInitialBlocks = new LinkedHashSet<>();
		mIsNondeterministic = isNondeterministic;

		if (initialPartition == null) {
			if (separateFinalsAndNonfinals) {
				mLargestBlockSizeInitialPartition = initializeFromAutomaton(worklistIntCall);
			} else {
				mLargestBlockSizeInitialPartition = initializeSingleton(worklistIntCall);
			}
		} else {
			mLargestBlockSizeInitialPartition =
					initializeFromPartition(initialPartition.getRelation(), worklistIntCall);
		}
	}

	@SuppressWarnings({ "unchecked", "static-method" })
	private STATE[] initializeArray(final int numberOfStates) {
		return (STATE[]) new Object[numberOfStates];
	}

	private int initializeFromAutomaton(final Worklist<STATE> worklistIntCall) {
		final int finalStatesSize = mOperand.getFinalStates().size();
		if (finalStatesSize > 0) {
			final Block finals = new Block(0, finalStatesSize);
			if (finalStatesSize < mStates.length) {
				// both final and non-final states
				final Block nonfinals = new Block(finalStatesSize, mStates.length);
				return initializeFromAutomatonFinalNonfinal(finals, nonfinals, worklistIntCall);
			}
			// only final states
			return initializeFromAutomatonSingleBlock(finals, worklistIntCall);
		}
		if (mStates.length == 0) {
			// no states at all
			return 0;
		}
		// TODO no final states, automaton is empty, could be simplified
		final Block nonfinals = new Block(finalStatesSize, mStates.length);
		return initializeFromAutomatonSingleBlock(nonfinals, worklistIntCall);
	}

	private int initializeFromAutomatonFinalNonfinal(final Partition<STATE>.Block finals,
			final Partition<STATE>.Block nonfinals, final Worklist<STATE> worklistIntCall) {
		final Collection<STATE> states = mOperand.getStates();
		int backwardPointer = mStates.length - 1;
		for (final STATE state : states) {
			assert !mState2PosAndBlock.containsKey(state) : "A state is duplicated in the automaton.";
			if (mOperand.isFinal(state)) {
				// add to the front
				mStates[mFirstInvalidIndex] = state;
				mState2PosAndBlock.put(state, new PosBlockPair(mFirstInvalidIndex, finals));
				++mFirstInvalidIndex;
			} else {
				// add to the back
				mStates[backwardPointer] = state;
				mState2PosAndBlock.put(state, new PosBlockPair(backwardPointer, nonfinals));
				--backwardPointer;
			}
		}
		if (!finals.isEmpty()) {
			worklistIntCall.add(finals);
		}
		if (!nonfinals.isEmpty()) {
			worklistIntCall.add(nonfinals);
		}
		return Math.max(finals.size(), nonfinals.size());
	}

	private int initializeFromAutomatonSingleBlock(final Partition<STATE>.Block block,
			final Worklist<STATE> worklistIntCall) {
		final Collection<STATE> states = mOperand.getStates();
		for (final STATE state : states) {
			assert !mState2PosAndBlock.containsKey(state) : "A state is duplicated in the automaton.";
			// add to the front
			mStates[mFirstInvalidIndex] = state;
			mState2PosAndBlock.put(state, new PosBlockPair(mFirstInvalidIndex, block));
			++mFirstInvalidIndex;
		}
		worklistIntCall.add(block);
		return block.size();
	}

	private int initializeSingleton(final Worklist<STATE> worklistIntCall) {
		final Block block = addBlock(mOperand.getStates());
		worklistIntCall.add(block);
		mSize = 1;
		return mStates.length;
	}

	private int initializeFromPartition(final Collection<Set<STATE>> initialPartition,
			final Worklist<STATE> worklistIntCall) {
		int largestBlockSizeInitialPartition = 0;
		for (final Set<STATE> states : initialPartition) {
			assert assertStatesSeparation(states) : "The initial partition must be consistent wrt. accepting states.";
			final Block block = addBlock(states);
			worklistIntCall.add(block);
			++mSize;
			largestBlockSizeInitialPartition = Math.max(largestBlockSizeInitialPartition, states.size());
		}
		assert mFirstInvalidIndex == mStates.length : "Some states are missing in the initial partition.";
		return largestBlockSizeInitialPartition;
	}

	/**
	 * Checks that the states in a given block are all either final or non-final.
	 *
	 * @param equivalenceClasses
	 *            partition passed in constructor
	 * @return true iff equivalence classes respect final status of states
	 */
	private boolean assertStatesSeparation(final Set<STATE> states) {
		final Iterator<STATE> it = states.iterator();
		assert (it.hasNext());
		final boolean isFinal = mOperand.isFinal(it.next());
		while (it.hasNext()) {
			if (isFinal != mOperand.isFinal(it.next())) {
				return false;
			}
		}
		return true;
	}

	private Partition<STATE>.Block addBlock(final Collection<STATE> states) {
		final Block block = new Block(mFirstInvalidIndex, mFirstInvalidIndex + states.size());
		for (final STATE state : states) {
			mStates[mFirstInvalidIndex] = state;
			assert !mState2PosAndBlock.containsKey(state) : "A state is duplicated in the initial partition.";
			mState2PosAndBlock.put(state, new PosBlockPair(mFirstInvalidIndex, block));
			++mFirstInvalidIndex;
		}
		return block;
	}

	public void mark(final STATE state) {
		final Partition<STATE>.PosBlockPair posBlockPair = mState2PosAndBlock.get(state);
		final Partition<STATE>.Block block = posBlockPair.mBlock;
		if (block.size() == 1) {
			// skip singleton blocks
			return;
		}
		final int pos = posBlockPair.mPos;
		final int afterMarked = block.mAfterMarked;
		if (pos >= afterMarked) {
			if (afterMarked == block.mFirst) {
				mMarkedBlocks.add(block);
			}
			// mark state
			if (pos != afterMarked) {
				// swap with the state at the border
				final STATE swapState = mStates[afterMarked];
				mStates[pos] = swapState;
				mState2PosAndBlock.get(swapState).mPos = pos;
				mStates[afterMarked] = state;
				posBlockPair.mPos = afterMarked;
			}
			++block.mAfterMarked;
		}
	}

	// TODO revise parameters after returns work
	public void splitAll(final Collection<STATE> splitter, final boolean splitterHasMoreActionsIntCall,
			final boolean isIntCallSplit, final Worklist<STATE> worklistIntCall) {
		while (!mMarkedBlocks.isEmpty()) {
			final Block block = mMarkedBlocks.pop();
			if (block.mAfterMarked == block.mAfterLast) {
				// all states marked; no split necessary, just unmark all states
				block.mAfterMarked = block.mFirst;
				continue;
			}
			if (block.mAfterMarked == block.mFirst) {
				// nothing marked; no split necessary
				assert false : "This block was never marked, so it should not be a split candidate.";
				continue;
			}
			// some but not all states marked; split away the smaller part
			final Block newBlockSmaller;
			if (block.mAfterMarked < (block.mAfterLast - block.mFirst / 2)) {
				// first part is smaller
				newBlockSmaller = splitHelper(block.mFirst, block.mAfterMarked);
				block.mFirst = block.mAfterMarked;
			} else {
				// last part is smaller
				newBlockSmaller = splitHelper(block.mAfterMarked, block.mAfterLast);
				block.mAfterLast = block.mAfterMarked;
				block.mAfterMarked = block.mFirst;
			}

			// add new (smaller) block to worklist unconditionally
			worklistIntCall.add(newBlockSmaller);

			// add old (bigger) block to worklist conditionally
			if (mIsNondeterministic && !block.isInWorklistIntCall()) {
				// for nondeterministic automata
				worklistIntCall.add(block);
			} else if (block == splitter) {
				// for the old block being the splitter and incoming transition analysis not having finished
				if (isIntCallSplit && splitterHasMoreActionsIntCall) {
					assert !block.isInWorklistIntCall() : "The splitter should have been removed from the worklist.";
					worklistIntCall.add(block);
				}
			}
		}
	}

	private Partition<STATE>.Block splitHelper(final int first, final int afterLast) {
		++mSize;
		final Block newBlock = new Block(first, afterLast);
		for (int idx = first; idx < afterLast; ++idx) {
			mState2PosAndBlock.get(mStates[idx]).mBlock = newBlock;
		}
		return newBlock;
	}

	public void markInitialBlocks(final Iterable<STATE> initialStates) {
		assert mMarkedBlocks.isEmpty() : "Some blocks are still marked.";
		assert mInitialBlocks.isEmpty() : "Some blocks are already marked as being initial.";
		for (final STATE state : initialStates) {
			mInitialBlocks.add(getBlock(state));
		}
	}

	public int getLargestBlockSizeInitialPartition() {
		return mLargestBlockSizeInitialPartition;
	}

	@Override
	public Set<STATE> getContainingSet(final STATE elem) {
		return getBlock(elem);
	}

	@Override
	public int size() {
		return mSize;
	}

	@Override
	public Block getBlock(final STATE state) {
		return mState2PosAndBlock.get(state).mBlock;
	}

	@Override
	public Iterator<Set<STATE>> iterator() {
		// code duplication with other iterator method - I blame Java
		return new Iterator<Set<STATE>>() {
			private Block mNext = getBlock(mStates[0]);

			@Override
			public boolean hasNext() {
				return mNext != null;
			}

			@Override
			public Set<STATE> next() {
				final Block res = mNext;
				mNext = (res.mAfterLast == mStates.length) ? null : getBlock(mStates[res.mAfterLast]);
				return res;
			}
		};
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("{");
		int idx = 0;
		String separator = "";
		while (idx < mStates.length) {
			builder.append(separator);
			separator = " ";
			final Partition<STATE>.Block block = getBlock(mStates[idx]);
			builder.append(block.toString());
			idx = block.mAfterLast;
		}
		builder.append("}");
		return builder.toString();
	}

	@Override
	public Iterator<IBlock<STATE>> blocksIterator() {
		// code duplication with other iterator method - I blame Java
		return new Iterator<IBlock<STATE>>() {
			private Block mNext = (mStates.length == 0) ? null : getBlock(mStates[0]);

			@Override
			public boolean hasNext() {
				return mNext != null;
			}

			@Override
			public IBlock<STATE> next() {
				final Block res = mNext;
				mNext = (res.mAfterLast == mStates.length) ? null : getBlock(mStates[res.mAfterLast]);
				return res;
			}
		};
	}

	/**
	 * Data structure for blocks in a partition, specialized for Hopcroft-style minimization algorithms.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <STATE>
	 *            state type
	 */
	protected class Block implements IBlock<STATE>, Set<STATE> {
		private int mFirst;
		private int mAfterLast;
		private int mAfterMarked;
		private boolean mInWorklistIntCall;
		private boolean mInWorklistRet;

		public Block(final int first, final int last) {
			assert first < last : "A block must contain at least one element.";
			mFirst = first;
			mAfterLast = last;
			mAfterMarked = mFirst;
		}

		public boolean isInWorklistIntCall() {
			return mInWorklistIntCall;
		}

		public void addToWorklistIntCall() {
			assert !mInWorklistIntCall : "Block already was in worklist IntCall.";
			mInWorklistIntCall = true;
		}

		public void removeFromWorklistIntCall() {
			assert mInWorklistIntCall : "Block was not in worklist Ret.";
			mInWorklistIntCall = false;
		}

		public void addToWorklistRet() {
			assert !mInWorklistRet : "Block already was in worklist Ret.";
			mInWorklistRet = true;
		}

		public void removeFromWorklistRet() {
			assert mInWorklistRet : "Block was not in worklist Ret.";
			mInWorklistRet = false;
		}

		@Override
		public Iterator<STATE> iterator() {
			assert mAfterMarked == mFirst;
			return new Iterator<STATE>() {
				private int mIdx = mFirst;

				@Override
				public boolean hasNext() {
					return mIdx < mAfterLast;
				}

				@Override
				public STATE next() {
					return mStates[mIdx++];
				}
			};
		}

		@Override
		public boolean isInitial() {
			return mInitialBlocks.contains(this);
		}

		@Override
		public boolean isFinal() {
			return mOperand.isFinal(mStates[mFirst]);
		}

		@Override
		public STATE minimize(final IMergeStateFactory<STATE> stateFactory) {
			return stateFactory.merge(getStates());
		}

		@Override
		public boolean isRepresentativeIndependentInternalsCalls() {
			/*
			 * This method should only be called after refinement has terminated, and then we have computed a direct
			 * bisimulation (for NFA).
			 */
			return true;
		}

		@Override
		public int size() {
			return mAfterLast - mFirst;
		}

		@Override
		public boolean isEmpty() {
			return false;
		}

		private Collection<STATE> getStates() {
			final Collection<STATE> collection = new ArrayList<>(size());
			forEach(collection::add);
			return collection;
		}

		@Override
		public Object[] toArray() {
			return Arrays.copyOfRange(mStates, mFirst, mAfterLast);
		}

		@Override
		public boolean contains(final Object o) {
			throw new UnsupportedOperationException();
		}

		@Override
		public <T> T[] toArray(final T[] a) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean add(final STATE e) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean remove(final Object o) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean containsAll(final Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean addAll(final Collection<? extends STATE> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean retainAll(final Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean removeAll(final Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void clear() {
			throw new UnsupportedOperationException();
		}

		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			String append = "";
			builder.append("<");
			int i = mFirst;
			for (; i < mAfterMarked; ++i) {
				builder.append(append);
				append = ", ";
				builder.append(mStates[i]);
			}
			builder.append("|");
			append = " ";
			for (; i < mAfterLast; ++i) {
				builder.append(append);
				append = ", ";
				builder.append(mStates[i]);
			}
			builder.append(">");
			return builder.toString();
		}
	}

	private class PosBlockPair {
		private int mPos;
		private Block mBlock;

		public PosBlockPair(final int pos, final Block block) {
			mPos = pos;
			mBlock = block;
		}

		@Override
		public String toString() {
			return "PosBlockPair [pos=" + mPos + ", block=" + mBlock + "]";
		}
	}
}
