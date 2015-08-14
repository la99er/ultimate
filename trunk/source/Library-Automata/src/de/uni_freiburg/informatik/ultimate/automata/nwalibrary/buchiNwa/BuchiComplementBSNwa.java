/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.PowersetIterator;

	

/**
 * Buchi Complementation based on the algorithm proposed by Frantisek Blahoudek
 * and Jan Stejcek. This complementation is only sound for a special class of
 * automata whose working title is TABA (termination analysis Büchi automata).
 * @author heizmann@informatik.uni-freiburg.de
 */
public class BuchiComplementBSNwa<LETTER,STATE> implements INestedWordAutomatonSimple<LETTER,STATE> {
	
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Operand;
	
	private final NestedWordAutomatonCache<LETTER, STATE> m_Cache;
	
	private final StateFactory<STATE> m_StateFactory;
	
	private final StateWithRankInfo<STATE> m_EmptyStackStateWRI;
	
	/**
	 * Maps BlaStState to its representative in the resulting automaton.
	 */
	private final Map<LevelRankingState<LETTER,STATE>,STATE> m_det2res =
		new HashMap<LevelRankingState<LETTER,STATE>, STATE>();
	
	/**
	 * Maps a state in resulting automaton to the BlaStState for which it
	 * was created.
	 */
	private final Map<STATE, LevelRankingState<LETTER,STATE>> m_res2det =
		new HashMap<STATE, LevelRankingState<LETTER,STATE>>();
	
	
	public BuchiComplementBSNwa(IUltimateServiceProvider services,
			INestedWordAutomatonSimple<LETTER,STATE> operand,
			StateFactory<STATE> stateFactory) throws OperationCanceledException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_StateFactory = stateFactory;
		m_Cache = new NestedWordAutomatonCache<LETTER, STATE>(
				m_Services,
				operand.getInternalAlphabet(), operand.getCallAlphabet(), 
				operand.getReturnAlphabet(), m_StateFactory);
		m_EmptyStackStateWRI = new StateWithRankInfo<STATE>(getEmptyStackState());
		constructInitialState();
	}
	
	
	private void constructInitialState() {
		LevelRankingState<LETTER,STATE> lvlrk = new LevelRankingState<LETTER,STATE>(m_Operand);
		for (STATE state : m_Operand.getInitialStates()) {
			if (m_Operand.isFinal(state)) {
				lvlrk.addRank(m_EmptyStackStateWRI, state, 2, false);
			} else {
				lvlrk.addRank(m_EmptyStackStateWRI, state, 3, false);
			}
		}
		getOrAdd(true, lvlrk);
	}
	
	private class LevelRankingConstraintWithHistory extends LevelRankingConstraint<LETTER,STATE> {
		public LevelRankingConstraintWithHistory(
				INestedWordAutomatonSimple<LETTER, STATE> operand) {
			super(operand, 9783, true);
		}

		private final Set<DoubleDeckerWithRankInfo<STATE>> m_PredecessorWasAccepting = new HashSet<DoubleDeckerWithRankInfo<STATE>>();

		protected void addConstaint(StateWithRankInfo<STATE> down, STATE up, Integer rank,
				boolean oCandidate, boolean predecessorWasAccepting) {
			if (predecessorWasAccepting) {
				m_PredecessorWasAccepting.add(new DoubleDeckerWithRankInfo<STATE>(down, up));
			}
			super.addConstaint(down, up, rank, oCandidate);
		}

		public Set<DoubleDeckerWithRankInfo<STATE>> getPredecessorWasAccepting() {
			return m_PredecessorWasAccepting;
		}
		
		
		
	}
	
	
	
	/**
	 * Return state of result automaton that represents detState. If no such
	 * state was constructed yet, construct it.
	 */
	private STATE getOrAdd(boolean isInitial, 
			LevelRankingState<LETTER,STATE> lvlrk) {
		STATE resState = m_det2res.get(lvlrk);
		if (resState == null) {
			resState = m_StateFactory.buchiComplementFKV(lvlrk);
			m_det2res.put(lvlrk, resState);
			m_res2det.put(resState, lvlrk);
			m_Cache.addState(isInitial, lvlrk.isOempty(), resState);
		} else {
			assert !isInitial;
		}
		return resState;
	}
	
	@Override
	public Iterable<STATE> getInitialStates() {
		return m_Cache.getInitialStates();
	}


	@Override
	public Set<LETTER> getInternalAlphabet() {
		return m_Operand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return m_Operand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return m_Operand.getReturnAlphabet();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_StateFactory;
	}
	
	@Override
	public boolean isInitial(STATE state) {
		return m_Cache.isInitial(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return m_Cache.isFinal(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return m_Cache.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		return m_Operand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		return m_Operand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		return m_Operand.getReturnAlphabet();
	}
	
	private LevelRankingConstraintWithHistory computeSuccLevelRankingConstraints_Internal(
			STATE state, LETTER letter) {
		LevelRankingConstraintWithHistory lrcwh = new LevelRankingConstraintWithHistory(m_Operand);
		LevelRankingState<LETTER,STATE> lvlrkState = m_res2det.get(state);
		for (StateWithRankInfo<STATE> down : lvlrkState.getDownStates()) {
			for (StateWithRankInfo<STATE> up : lvlrkState.getUpStates(down)) {
				boolean oCandidate = lvlrkState.isOempty() || up.isInO();
				for (OutgoingInternalTransition<LETTER, STATE> trans : 
								m_Operand.internalSuccessors(up.getState(), letter)) {
					lrcwh.addConstaint(down, trans.getSucc(), up.getRank(), oCandidate, m_Operand.isFinal(up.getState()));
				}
			}
		}
		return lrcwh;
	}
	
	private LevelRankingConstraintWithHistory computeSuccLevelRankingConstraints_Call(
			STATE state, LETTER letter) {
		LevelRankingConstraintWithHistory lrcwh = new LevelRankingConstraintWithHistory(m_Operand);
		LevelRankingState<LETTER,STATE> lvlrkState = m_res2det.get(state);
		for (StateWithRankInfo<STATE> down : lvlrkState.getDownStates()) {
			for (StateWithRankInfo<STATE> up : lvlrkState.getUpStates(down)) {
				boolean oCandidate = lvlrkState.isOempty() || up.isInO();
				for (OutgoingCallTransition<LETTER, STATE> trans : 
								m_Operand.callSuccessors(up.getState(), letter)) {
					lrcwh.addConstaint(up, trans.getSucc(), up.getRank(), oCandidate, m_Operand.isFinal(up.getState()));
				}
			}
		}
		return lrcwh;
	}
	
	private LevelRankingConstraintWithHistory computeSuccLevelRankingConstraints_Return(
			STATE state, STATE hier, LETTER letter) {
		LevelRankingConstraintWithHistory lrcwh = new LevelRankingConstraintWithHistory(m_Operand);
		LevelRankingState<LETTER,STATE> lvlrkState = m_res2det.get(state);
		LevelRankingState<LETTER,STATE> lvlrkHier = m_res2det.get(hier);
		for (StateWithRankInfo<STATE> downHier : lvlrkHier.getDownStates()) {
			for (StateWithRankInfo<STATE> upHier : lvlrkHier.getUpStates(downHier)) {
				if (!lvlrkState.getDownStates().contains(upHier)) {
					continue;
				}
				for (StateWithRankInfo<STATE> up : lvlrkState.getUpStates(upHier)) {
					boolean oCandidate = lvlrkState.isOempty() || up.isInO();
					for (OutgoingReturnTransition<LETTER, STATE> trans : 
						m_Operand.returnSucccessors(up.getState(), upHier.getState(), letter)) {
						lrcwh.addConstaint(downHier, trans.getSucc(), up.getRank(), oCandidate, m_Operand.isFinal(up.getState()));
					}
				}
			}
		}
		return lrcwh;
	}


	private List<LevelRankingState<LETTER, STATE>> computeSuccLevelRankingStates(
			LevelRankingConstraintWithHistory lrcwh) {
		List<LevelRankingState<LETTER, STATE>> succLvls = new ArrayList<LevelRankingState<LETTER,STATE>>();
		Set<DoubleDeckerWithRankInfo<STATE>> allDoubleDeckersWithVoluntaryDecrease = 
				computeDoubleDeckersWithVoluntaryDecrease(lrcwh);
		Iterator<Set<DoubleDeckerWithRankInfo<STATE>>> it = 
				new PowersetIterator<DoubleDeckerWithRankInfo<STATE>>(allDoubleDeckersWithVoluntaryDecrease);
		while(it.hasNext()) {
			Set<DoubleDeckerWithRankInfo<STATE>> subset = it.next();
			LevelRankingState<LETTER, STATE> succCandidate = computeLevelRanking(lrcwh, subset);
			if (succCandidate != null) {
				succLvls.add(succCandidate);
			}
		}
		return succLvls;
	}


	private Set<DoubleDeckerWithRankInfo<STATE>> computeDoubleDeckersWithVoluntaryDecrease(
			LevelRankingConstraintWithHistory lrcwh) {
		Set<DoubleDeckerWithRankInfo<STATE>> doubleDeckersWithVoluntaryDecrease = new HashSet<DoubleDeckerWithRankInfo<STATE>>();
		for (DoubleDeckerWithRankInfo<STATE> predWasAccepting : lrcwh.getPredecessorWasAccepting()) {
			int rank = lrcwh.getRank(predWasAccepting.getDown(), predWasAccepting.getUp());
			if (BuchiComplementFKVNwa.isEven(rank) && !m_Operand.isFinal(predWasAccepting.getUp())) {
				doubleDeckersWithVoluntaryDecrease.add(predWasAccepting);
			}
		}
		return doubleDeckersWithVoluntaryDecrease;
	}


	private LevelRankingState<LETTER, STATE> computeLevelRanking(LevelRankingConstraintWithHistory lrcwh,
			Set<DoubleDeckerWithRankInfo<STATE>> doubleDeckersWithVoluntaryDecrease) {
		LevelRankingState<LETTER, STATE> result = new LevelRankingState<LETTER, STATE>(m_Operand);
		for (StateWithRankInfo<STATE> down : lrcwh.getDownStates()) {
			for (StateWithRankInfo<STATE> up : lrcwh.getUpStates(down)) {
				final boolean oCandidate = up.isInO();
				final boolean inO;
				int rank = up.getRank();
				switch (rank) {
				case 3:
					if (m_Operand.isFinal(up.getState())) {
						rank = 2;
						inO = oCandidate;
					} else {
						inO = false;
					}
					break;
				case 2:
					if (doubleDeckersWithVoluntaryDecrease.contains(new DoubleDecker<StateWithRankInfo<STATE>>(down, up))) {
						rank = 1;
						inO = false;
					} else {
						inO = oCandidate;
					}
					break;
				case 1:
					if (m_Operand.isFinal(up.getState())) {
						return null;
					} else {
						inO = false;
					}
					break;
				default:
					throw new AssertionError("no other ranks allowed");
				}
				result.addRank(down, up.getState(), rank, inO);
			}
		}
		return result;
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succInternal(state, letter);
		if (succs == null) {
			LevelRankingConstraintWithHistory lrcwh = computeSuccLevelRankingConstraints_Internal(
					state, letter);
			List<LevelRankingState<LETTER, STATE>> succLvls = computeSuccLevelRankingStates(lrcwh);
			for (LevelRankingState<LETTER, STATE> succLvl : succLvls) {
				STATE resSucc = getOrAdd(false, succLvl);
				m_Cache.addInternalTransition(state, letter, resSucc);
			}
		}
		return m_Cache.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		for (LETTER letter : getInternalAlphabet()) {
			internalSuccessors(state, letter);
		}
		return m_Cache.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succCall(state, letter);
		if (succs == null) {
			LevelRankingConstraintWithHistory lrcwh = computeSuccLevelRankingConstraints_Call(
					state, letter);
			List<LevelRankingState<LETTER, STATE>> succLvls = computeSuccLevelRankingStates(lrcwh);
			for (LevelRankingState<LETTER, STATE> succLvl : succLvls) {
				STATE resSucc = getOrAdd(false, succLvl);
				m_Cache.addCallTransition(state, letter, resSucc);
			}
		}
		return m_Cache.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		for (LETTER letter : getCallAlphabet()) {
			callSuccessors(state, letter);
		}
		return m_Cache.callSuccessors(state);
	}



	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		Collection<STATE> succs = m_Cache.succReturn(state, hier, letter);
		if (succs == null) {
			LevelRankingConstraintWithHistory lrcwh = computeSuccLevelRankingConstraints_Return(
					state, hier, letter);
			List<LevelRankingState<LETTER, STATE>> succLvls = computeSuccLevelRankingStates(lrcwh);
			for (LevelRankingState<LETTER, STATE> succLvl : succLvls) {
				STATE resSucc = getOrAdd(false, succLvl);
				m_Cache.addReturnTransition(state, hier, letter, resSucc);
			}
		}
		return m_Cache.returnSucccessors(state, hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		for (LETTER letter : getReturnAlphabet()) {
			returnSucccessors(state, hier, letter);
		}
		return m_Cache.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public int size() {
		return m_Cache.size();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		throw new UnsupportedOperationException();	}

	@Override
	public String sizeInformation() {
		return "size Information not available";
	}
	
	
	
	
	



}
