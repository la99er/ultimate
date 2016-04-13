/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
/**
 * Buchi automata state space reduction algorithm based on the following paper:
 * "Fair simulation relations, parity games and state space reduction for
 * Buchi automata" - Etessami, Wilke and Schuller.
 * 
 * Algorithm optimized to work using strongly connected components.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.direct;

import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ESimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;

/**
 * Simulation that realizes <b>direct simulation</b> for reduction of a given
 * buechi automaton.<br/>
 * Once created it starts the simulation, results can then be get by using
 * {@link #getResult()}.<br/>
 * <br/>
 * 
 * For more information on the type of simulation see {@link DirectGameGraph}.
 * <br/>
 * <br/>
 * 
 * The algorithm runs in <b>O(n^3 * k)</b> time and <b>O(n * k)</b> space where
 * n is the amount of states and k the amount of transitions from the inputed
 * automaton.<br/>
 * The algorithm is based on the paper: <i>Fair simulation relations, parity
 * games, and state space reduction for büchi automata<i> by <i>Etessami, Wilke
 * and Schuller</i>.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public final class DirectSimulation<LETTER, STATE> extends ASimulation<LETTER, STATE> {

	/**
	 * Game graph that is used for simulation calculation.
	 */
	private final AGameGraph<LETTER, STATE> m_Game;

	/**
	 * Creates a new direct simulation with a given graph that tries to reduce
	 * the given buechi automaton using <b>direct simulation</b>.<br/>
	 * After construction the simulation starts and results can be get by using
	 * {@link #getResult()}.<br/>
	 * <br/>
	 * 
	 * For correctness its important that the inputed automaton has <b>no dead
	 * ends</b> nor <b>duplicate transitions</b>.
	 * 
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation.
	 * @param logger
	 *            Logger of the Ultimate framework.
	 * @param useSCCs
	 *            If the simulation calculation should be optimized using SCC,
	 *            Strongly Connected Components.
	 * @param stateFactory
	 *            The state factory used for creating states.
	 * @param game
	 *            The game graph to use for simulation.
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public DirectSimulation(final IProgressAwareTimer progressTimer, final Logger logger, final boolean useSCCs,
			final StateFactory<STATE> stateFactory, final AGameGraph<LETTER, STATE> game)
					throws OperationCanceledException {
		super(progressTimer, logger, useSCCs, stateFactory, ESimulationType.DIRECT);

		game.setSimulationPerformance(getSimulationPerformance());
		m_Game = game;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.ASimulation#calcBestNghbMeasure(de.uni_freiburg.informatik
	 * .ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex,
	 * int, java.util.Set)
	 */
	@Override
	protected int calcBestNghbMeasure(final Vertex<LETTER, STATE> vertex, final int localInfinity,
			final Set<Vertex<LETTER, STATE>> scc) {
		// DirectSimulation needs infinity for spoiler vertices without
		// successors instead of 0. Direct simulation uses a hack to exclude
		// winning Spoiler vertices by removing all their transitions which then
		// should not indicate a winning for Duplicator.
		if (vertex.isSpoilerVertex() && !getGameGraph().hasSuccessors(vertex)) {
			return getGameGraph().getGlobalInfinity();
		} else {
			return super.calcBestNghbMeasure(vertex, localInfinity, scc);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.ASimulation#getGameGraph()
	 */
	@Override
	protected AGameGraph<LETTER, STATE> getGameGraph() {
		return m_Game;
	}
}
