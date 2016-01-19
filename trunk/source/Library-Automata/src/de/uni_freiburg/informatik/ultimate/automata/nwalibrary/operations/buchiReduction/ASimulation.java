/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.PriorityQueue;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.performance.CountingMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.performance.MultipleDataOption;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.performance.SimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.performance.TimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.VertexPmReverseComparator;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultStronglyConnectedComponentFactory;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Abstract class for simulations which can be used for <b>reducing buechi
 * automaton</b>.<br/>
 * <br/>
 * 
 * The simulation sets a {@link AGameGraph} object up that is based on the
 * original buechi automaton. It then simulates the game, explained in
 * {@link AGameGraph}, and calculates so called progress measure for every
 * vertex of the graph.<br/>
 * The simulation does so by comparing vertices with their neighbors and
 * choosing the optimal transition based on which player is at turn.
 * <i>Duplicator</i> wants to decrease the progress measure, which is done by
 * visiting vertices with priority 0, and <i>Spoiler</i> wants to increase it by
 * visiting odd priorities.<br/>
 * <br/>
 * 
 * For correctness its important that the inputed automaton has <b>no dead
 * ends</b> nor <b>duplicate transitions</b>.<br/>
 * <br/>
 * 
 * The exact conditions are determined by the type of game graph. If, for a
 * vertex (q0, q1), the progress measure does not reach infinity we say q1
 * simulates q0.<br/>
 * This simulation information can then be used for buechi reduction. In some
 * types of simulation such simulating states can be merged without changing the
 * underlying language.<br/>
 * <br/>
 * 
 * The simulation automatically starts after construction and its result can be
 * accessed by using {@link #getResult()}.<br/>
 * <br/>
 * 
 * For game graphs see {@link AGameGraph}, for information on the magic infinity
 * bound see {@link AGameGraph#getGlobalInfinity()}.
 * 
 * @author Daniel Tischner
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public abstract class ASimulation<LETTER, STATE> {

	/**
	 * The logger used by the Ultimate framework.
	 */
	private final Logger m_Logger;
	/**
	 * Holds information about the performance of the simulation after usage.
	 */
	private final SimulationPerformance m_Performance;
	/**
	 * Timer used for responding to timeouts and operation cancellation.
	 */
	private final IProgressAwareTimer m_ProgressTimer;
	/**
	 * The resulting possible reduced buechi automaton.
	 */
	private INestedWordAutomatonOldApi<LETTER, STATE> m_Result;
	/**
	 * The object that computes the SCCs of a given buechi automaton.
	 */
	private SccComputation<Vertex<LETTER, STATE>, StronglyConnectedComponent<Vertex<LETTER, STATE>>> m_SccComp;
	/**
	 * The state factory used for creating states.
	 */
	private final StateFactory<STATE> m_StateFactory;
	/**
	 * If the simulation calculation should be optimized using SCC, Strongly
	 * Connected Components.
	 */
	private boolean m_UseSCCs;
	/**
	 * Comparator that compares two given vertices by their progress measure
	 * whereas a higher measure gets favored before a smaller.<br/>
	 * This is used to implement the @link {@link #m_WorkingList working list}
	 * as a priority queue that first works vertices with high measures.
	 */
	private VertexPmReverseComparator<LETTER, STATE> m_VertexComp;
	/**
	 * The internal working list of the simulation that, in general, gets
	 * initiated with vertices that have priority 1. It contains vertices that
	 * benefit from a progress measure update of its neighbors and therefore
	 * they need to be updated itself.<br/>
	 * The list is implemented as priority queue that first works vertices with
	 * the highest progress measure.
	 */
	private PriorityQueue<Vertex<LETTER, STATE>> m_WorkingList;

	/**
	 * Creates a new simulation that initiates all needed data structures and
	 * fields.
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
	 * @param simType
	 *            Type of the simulation implementing.
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public ASimulation(final IProgressAwareTimer progressTimer, final Logger logger, final boolean useSCCs,
			final StateFactory<STATE> stateFactory, final SimulationType simType) throws OperationCanceledException {
		m_ProgressTimer = progressTimer;
		m_Logger = logger;
		m_UseSCCs = useSCCs;
		m_StateFactory = stateFactory;
		m_VertexComp = new VertexPmReverseComparator<>();

		m_SccComp = null;

		m_Performance = new SimulationPerformance(simType, useSCCs);
	}

	/**
	 * Gets the resulting possible reduced buechi automaton.
	 * 
	 * @return The resulting possible reduced buechi automaton.
	 */
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult() {
		return m_Result;
	}

	/**
	 * Gets the performance of the simulation.
	 * 
	 * @return The performance of the simulation.
	 */
	public SimulationPerformance getSimulationPerformance() {
		return m_Performance;
	}

	/**
	 * Gets t state factory used for creating states.
	 * 
	 * @return The state factory used for creating states.
	 */
	public StateFactory<STATE> getStateFactory() {
		return m_StateFactory;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();
		String lineSeparator = System.lineSeparator();
		// Header
		result.append("SimulationResults sr = (");

		// Properties
		result.append(lineSeparator + "\tuseSCCs = " + isUsingSCCs());
		result.append(lineSeparator + "\tglobalInfinity = " + getGameGraph().getGlobalInfinity());
		if (getResult() != null) {
			result.append(lineSeparator + "\tbuechi size after = " + getResult().size() + " states");
		}

		// Progress Measure
		result.append(lineSeparator + "\tprogress measure = {");
		for (SpoilerVertex<LETTER, STATE> vertex : getGameGraph().getSpoilerVertices()) {
			int localInfinity = getGameGraph().getGlobalInfinity();
			if (isUsingSCCs()) {
				for (StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : getSccComp().getSCCs()) {
					if (scc.getNodes().contains(vertex)) {
						localInfinity = calculateInfinityOfSCC(scc);
					}
				}
			}
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), pm:"
					+ vertex.getPM(null, getGameGraph().getGlobalInfinity()) + " of " + localInfinity + ">");
		}
		for (DuplicatorVertex<LETTER, STATE> vertex : getGameGraph().getDuplicatorVertices()) {
			int localInfinity = getGameGraph().getGlobalInfinity();
			if (isUsingSCCs()) {
				for (StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : getSccComp().getSCCs()) {
					if (scc.getNodes().contains(vertex)) {
						localInfinity = calculateInfinityOfSCC(scc);
					}
				}
			}
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), pm:" + vertex.getPM(null, getGameGraph().getGlobalInfinity()) + " of " + localInfinity + ">");
		}
		result.append(lineSeparator + "\t},");

		// Best Neighbor Measure
		result.append(lineSeparator + "\tbest neighbor measure = {");
		for (SpoilerVertex<LETTER, STATE> vertex : getGameGraph().getSpoilerVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), bnm:"
					+ vertex.getBEff() + ">");
		}
		for (DuplicatorVertex<LETTER, STATE> vertex : getGameGraph().getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), bnm:" + vertex.getBEff() + ">");
		}
		result.append(lineSeparator + "\t},");

		// Neighbor counter
		result.append(lineSeparator + "\tneighbor counter = {");
		for (SpoilerVertex<LETTER, STATE> vertex : getGameGraph().getSpoilerVertices()) {
			result.append(
					lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), nc:" + vertex.getC() + ">");
		}
		for (DuplicatorVertex<LETTER, STATE> vertex : getGameGraph().getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), nc:" + vertex.getC() + ">");
		}
		result.append(lineSeparator + "\t},");

		// Footer
		result.append(lineSeparator + ");");

		return result.toString();
	}

	/**
	 * Adds a given vertex to the working list and updates its own working list
	 * flag.
	 * 
	 * @param vertex
	 *            Vertex to add
	 */
	protected void addVertexToWorkingList(final Vertex<LETTER, STATE> vertex) {
		m_WorkingList.add(vertex);
		vertex.setInWL(true);
	}

	/**
	 * Calculates the best neighbor measure for a given vertex based on its
	 * local infinity and its containing SCC.<br/>
	 * <br/>
	 * 
	 * If the vertex has no successors the corresponding player looses,
	 * <i>infinity</i> is returned for a {@link DuplicatorVertex} and 0 for a
	 * {@link SpoilerVertex}.<br/>
	 * For a {@link DuplicatorVertex} the minimal progress measure of its
	 * successor is returned, maximal for a {@link SpoilerVertex}.<br/>
	 * The returned then gets decreased based on the priority of the given
	 * vertex.
	 * 
	 * @param vertex
	 *            The given vertex to calculate for
	 * @param localInfinity
	 *            The local infinity in the containing SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The containing SCC or <tt>null</tt> if not used
	 * @return The best neighbor measure of the vertex
	 */
	protected int calcBestNghbMeasure(final Vertex<LETTER, STATE> vertex, final int localInfinity,
			final Set<Vertex<LETTER, STATE>> scc) {
		boolean isDuplicatorVertex = vertex.isDuplicatorVertex();

		// If there are no successors the corresponding player looses
		if (!getGameGraph().hasSuccessors(vertex)) {
			if (isDuplicatorVertex) {
				return getGameGraph().getGlobalInfinity();
			} else {
				return 0;
			}
		}

		// Initiate the known optimum, big for duplicator and small for spoiler
		int optimum;
		if (isDuplicatorVertex) {
			optimum = getGameGraph().getGlobalInfinity();
		} else {
			optimum = 0;
		}

		// The optimum is the minimal progress measure of its successors for
		// Duplicator and maximal for Spoiler
		for (Vertex<LETTER, STATE> succ : getGameGraph().getSuccessors(vertex)) {
			int progressMeasure = succ.getPM(scc, getGameGraph().getGlobalInfinity());
			if (isDuplicatorVertex) {
				if (progressMeasure < optimum) {
					optimum = progressMeasure;
				}
			} else {
				if (progressMeasure > optimum) {
					optimum = progressMeasure;
				}
			}
		}

		// Decrease the optimum based on the priority
		return decreaseVector(getGameGraph().getPriority(vertex), optimum, localInfinity);
	}

	/**
	 * Calculates the number of successors a vertex has that represent the best
	 * choice for it to go at.<br/>
	 * This is represented by the best neighbor measure of the vertex.
	 * 
	 * @param vertex
	 *            The vertex to calculate for
	 * @param localInfinity
	 *            The local infinity in the containing SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The containing SCC or <tt>null</tt> if not used
	 * @return The neighbor counter of the vertex
	 */
	protected int calcNghbCounter(final Vertex<LETTER, STATE> vertex, final int localInfinity,
			final Set<Vertex<LETTER, STATE>> scc) {
		// If there are no successors we have zero best neighbors
		if (!getGameGraph().hasSuccessors(vertex)) {
			return 0;
		}

		// Count the number of successors that have the best
		// neighbor measure from the perspective of the vertex and its priority
		int counter = 0;
		for (Vertex<LETTER, STATE> succ : getGameGraph().getSuccessors(vertex))
			if (decreaseVector(getGameGraph().getPriority(vertex), succ.getPM(scc, getGameGraph().getGlobalInfinity()),
					localInfinity) == vertex.getBEff()) {
				counter++;
			}
		return counter;
	}

	/**
	 * Calculates the local infinity bound of a given SCC. Which is the number
	 * of vertices in the SCC that have priority 1, plus one.<br/>
	 * In contrast to the {@link AGameGraph#getGlobalInfinity() global infinity
	 * of a game graph} this can be used to locally optimize the simulation
	 * calculation of a single SCC. This is because we can already be sure that
	 * we can visit the corresponding vertices infinite times after visiting
	 * them the local bound often.
	 * 
	 * @param scc
	 *            The SCC to calculate the local infinity for
	 * @return A, for the SCC, local optimal upper bound for infinity which is
	 *         the number of vertices in the SCC that have priority 1, plus one.
	 */
	protected int calculateInfinityOfSCC(final StronglyConnectedComponent<Vertex<LETTER, STATE>> scc) {
		int localInfinity = 0;
		for (Vertex<LETTER, STATE> vertex : scc.getNodes()) {
			if (getGameGraph().getPriority(vertex) == 1) {
				localInfinity++;
			}
		}
		localInfinity++;
		return localInfinity;
	}

	/**
	 * Creates and sets a new working list.
	 */
	protected void createWorkingList() {
		m_WorkingList = new PriorityQueue<>(m_VertexComp);
	}

	/**
	 * Decreases a given number based on a given index and a local infinity.
	 * <br/>
	 * The global infinity bound gets returned if the number has reached the
	 * local infinity bound. The number itself gets returned if the index is not
	 * zero and 0 if it is zero.
	 * 
	 * @param index
	 *            The index to reduce to
	 * @param vector
	 *            The number to reduce
	 * @param localInfinity
	 *            The local infinity in the containing SCC or global infinity if
	 *            not used
	 * @return Global infinity if reached local infinity, the inputed number if
	 *         index is not zero and 0 if it is.
	 */
	protected int decreaseVector(final int index, final int vector, final int localInfinity) {
		// Always return global infinity if greater than local infinity
		if (vector >= localInfinity) {
			return getGameGraph().getGlobalInfinity();
		}
		if (index == 0) {
			return 0;
		} else {
			return vector;
		}
	}

	/**
	 * Starts the simulation that calculates the corresponding progress measures
	 * to all vertices of the underlying game graph. After that it uses that
	 * information to possible reduce the inputed buechi automaton and finally
	 * assigns the result which then can be accessed by {@link #getResult()}.
	 * 
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	protected void doSimulation() throws OperationCanceledException {
		m_Performance.startTimeMeasure(TimeMeasure.OVERALL_TIME);
		m_Performance.startTimeMeasure(TimeMeasure.SIMULATION_ONLY_TIME);

		if (m_UseSCCs) { // calculate reduction with SCC
			m_Performance.startTimeMeasure(TimeMeasure.BUILD_SCC);
			DefaultStronglyConnectedComponentFactory<Vertex<LETTER, STATE>> sccFactory = new DefaultStronglyConnectedComponentFactory<>();
			GameGraphSuccessorProvider<LETTER, STATE> succProvider = new GameGraphSuccessorProvider<>(getGameGraph());
			m_SccComp = new SccComputation<>(m_Logger, succProvider, sccFactory, getGameGraph().getSize(),
					getGameGraph().getVertices());

			Iterator<StronglyConnectedComponent<Vertex<LETTER, STATE>>> iter = new LinkedList<StronglyConnectedComponent<Vertex<LETTER, STATE>>>(
					m_SccComp.getSCCs()).iterator();
			m_Performance.stopTimeMeasure(TimeMeasure.BUILD_SCC);
			while (iter.hasNext()) {
				StronglyConnectedComponent<Vertex<LETTER, STATE>> scc = iter.next();
				iter.remove();
				efficientLiftingAlgorithm(calculateInfinityOfSCC(scc), scc.getNodes());
			}
		} else { // calculate reduction w/o SCCs
			efficientLiftingAlgorithm(getGameGraph().getGlobalInfinity(), null);
			m_Performance.addTimeMeasureValue(TimeMeasure.BUILD_SCC, SimulationPerformance.NO_TIME_RESULT);
		}
		m_Performance.stopTimeMeasure(TimeMeasure.SIMULATION_ONLY_TIME);
		m_Result = getGameGraph().generateBuchiAutomatonFromGraph();

		long duration = m_Performance.stopTimeMeasure(TimeMeasure.OVERALL_TIME);
		// Add time building of the graph took to the overall time since this
		// happens outside of simulation
		long durationGraph = m_Performance.getTimeMeasureResult(TimeMeasure.BUILD_GRAPH_TIME,
				MultipleDataOption.ADDITIVE);
		if (durationGraph != SimulationPerformance.NO_TIME_RESULT) {
			duration += durationGraph;
			m_Performance.addTimeMeasureValue(TimeMeasure.OVERALL_TIME, durationGraph);
		}

		m_Logger.info((this.m_UseSCCs ? "SCC version" : "nonSCC version") + " took " + duration + " milliseconds.");
	}

	/**
	 * The actual simulation calculation algorithm which simulates the
	 * corresponding game defined by the type of {@link AGameGraph}.<br/>
	 * When finished the progress measures of given vertices determine a
	 * simulation relation that is used for reducing buechi automata.<br/>
	 * For a given vertex (q0, q1) we shall say q1 simulates q0 if its progress
	 * measure did not reach infinity.
	 * 
	 * @param localInfinity
	 *            The local infinity in the containing SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The containing SCC or <tt>null</tt> if not used
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	protected void efficientLiftingAlgorithm(final int localInfinity, final Set<Vertex<LETTER, STATE>> scc)
			throws OperationCanceledException {
		AGameGraph<LETTER, STATE> game = getGameGraph();
		int globalInfinity = game.getGlobalInfinity();

		// Initialize working list and the C value of all vertices
		createWorkingList();
		if (m_UseSCCs) {
			for (Vertex<LETTER, STATE> v : scc) {
				initWorkingListAndCWithVertex(v, localInfinity, scc);
			}
		} else {
			for (DuplicatorVertex<LETTER, STATE> v : game.getDuplicatorVertices()) {
				initWorkingListAndCWithVertex(v, localInfinity, scc);
			}
			for (SpoilerVertex<LETTER, STATE> v : game.getSpoilerVertices()) {
				initWorkingListAndCWithVertex(v, localInfinity, scc);
			}
		}

		// Work through the working list until its empty
		while (!m_WorkingList.isEmpty()) {
			m_Performance.increaseCountingMeasure(CountingMeasure.SIMULATION_STEPS);

			// Poll the current working vertex
			Vertex<LETTER, STATE> v = pollVertexFromWorkingList();

			// Remember old progress measure of the working vertex
			int t = v.getPM(scc, globalInfinity);

			// Update values of the working vertex
			v.setBEff(calcBestNghbMeasure(v, localInfinity, scc));
			v.setC(calcNghbCounter(v, localInfinity, scc));
			v.setPM(increaseVector(getGameGraph().getPriority(v), v.getBEff(), localInfinity));

			// Work through its predecessors and possibly add them
			// to the working list since they may be interested in
			// the changes of the working vertex
			if (!game.hasPredecessors(v))
				continue;
			for (Vertex<LETTER, STATE> w : game.getPredecessors(v)) {
				if (m_UseSCCs && !scc.contains(w))
					continue;

				// If the working vertex has increased its progress
				// measure from the perspective of the predecessor and
				// its priority
				if (!w.isInWL() && decreaseVector(getGameGraph().getPriority(w), v.getPM(scc, globalInfinity),
						localInfinity) > w.getBEff()) {
					// A Duplicator vertex is only interested in an increased
					// progress measure if the working vertex was its
					// best choice previously and it has no better
					// alternative now
					if (w.isDuplicatorVertex()
							&& decreaseVector(getGameGraph().getPriority(w), t, localInfinity) == w.getBEff()) {
						if (w.getC() == 1) {
							// It has no better alternative,
							// adding to working list
							addVertexToWorkingList(w);
						}
						if (w.getC() > 1) {
							// It has a better alternative, reducing number of
							// neighbors that represent the best choice for the
							// predecessor
							w.setC(w.getC() - 1);
						}
					} else if (w.isSpoilerVertex()) {
						// A Spoiler vertex is always interested in an increased
						// progress measure
						addVertexToWorkingList(w);
					}
				}
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
				m_Logger.debug("Stopped in efficientLiftingAlgorithm");
				throw new OperationCanceledException(this.getClass());
			}
		}
	}

	/**
	 * Gets the {@link AGameGraph} used for this simulation.
	 * 
	 * @return The {@link AGameGraph} used for this simulation.
	 */
	protected abstract AGameGraph<LETTER, STATE> getGameGraph();

	/**
	 * Gets the logger used by the Ultimate framework.
	 * 
	 * @return The logger used by the Ultimate framework.
	 */
	protected Logger getLogger() {
		return m_Logger;
	}

	/**
	 * Gets the timer used for responding to timeouts and operation
	 * cancellation.
	 * 
	 * @return The timer used for responding to timeouts and operation
	 *         cancellation.
	 */
	protected IProgressAwareTimer getProgressTimer() {
		return m_ProgressTimer;
	}

	/**
	 * Gets the object that is used for computing the SCCs of a given buechi
	 * automaton.
	 * 
	 * @return The object that is used for computing the SCCs of a given buechi
	 *         automaton.
	 */
	protected SccComputation<Vertex<LETTER, STATE>, StronglyConnectedComponent<Vertex<LETTER, STATE>>> getSccComp() {
		return m_SccComp;
	}

	/**
	 * Gets the current working list of the simulation.
	 * 
	 * @return The current working list of the simulation.
	 */
	protected PriorityQueue<Vertex<LETTER, STATE>> getWorkingList() {
		return m_WorkingList;
	}

	/**
	 * Increases a given number by using a given index and a local infinity.
	 * <br/>
	 * Returning the global infinity if number has reached the local infinity
	 * bound, a decreased vector for a index that is not one.<br/>
	 * For a index of one it increases the given number and returns it or global
	 * infinity if reached the local infinity bound.
	 * 
	 * @param index
	 *            The given index to increase from
	 * @param vector
	 *            The number to increase
	 * @param localInfinity
	 *            The local infinity in the containing SCC or global infinity if
	 *            not used
	 * @return Global infinity if reached local infinity, the inputed number if
	 *         index is two, 0 if it is zero and increased by one if the index
	 *         it is one.
	 */
	protected int increaseVector(final int index, final int vector, final int localInfinity) {
		// Always return global infinity if greater than local infinity
		if (vector >= localInfinity) {
			return getGameGraph().getGlobalInfinity();
		}
		if (index == 1) {
			int tempVector = vector + 1;
			// Always return global infinity if greater than local infinity
			if (tempVector == localInfinity) {
				return getGameGraph().getGlobalInfinity();
			}
			return tempVector;
		} else {
			return decreaseVector(index, vector, localInfinity);
		}
	}

	/**
	 * Initializes a given vertex for the current simulation calculation by
	 * possibly adding it to the working list and initializing its values.<br/>
	 * Used by {@link #initSimulation(int, Set)}.
	 * 
	 * @param vertex
	 *            Vertex to initialize
	 * @param localInfinity
	 *            The local infinity bound of the used SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The currently for simulation used SCC or <tt>null</tt> if not
	 *            used
	 */
	protected void initWorkingListAndCWithVertex(final Vertex<LETTER, STATE> vertex, final int localInfinity,
			final Set<Vertex<LETTER, STATE>> scc) {
		boolean isDeadEnd = !getGameGraph().hasSuccessors(vertex);
		boolean doesChangeWithUpdate = vertex.getPM(scc, getGameGraph().getGlobalInfinity()) != update(vertex,
				localInfinity, scc);

		// Possibly add vertex to working list
		if (isDeadEnd || doesChangeWithUpdate) {
			addVertexToWorkingList(vertex);
		}

		// Initialize C value of vertex
		if (m_UseSCCs) {
			vertex.setC(calcNghbCounter(vertex, localInfinity, scc));
		} else {
			if (getGameGraph().hasSuccessors(vertex)) {
				vertex.setC(getGameGraph().getSuccessors(vertex).size());
			} else {
				vertex.setC(0);
			}

		}
	}

	/**
	 * If the simulation calculation gets optimized by using SCC, Strongly
	 * Connected Components.
	 * 
	 * @return True if the simulation calculation gets optimized by using SCC,
	 *         false if not.
	 */
	protected boolean isUsingSCCs() {
		return m_UseSCCs;
	}

	/**
	 * Retrieves and removes the head of the working list. Also updates the
	 * working list flag of the vertex.
	 * 
	 * @return The head of the working list, or <tt>null</tt> if it is empty.
	 */
	protected Vertex<LETTER, STATE> pollVertexFromWorkingList() {
		Vertex<LETTER, STATE> polledVertex = m_WorkingList.poll();
		if (polledVertex != null) {
			polledVertex.setInWL(false);
		}
		return polledVertex;
	}

	/**
	 * Sets the result of the simulation calculation, a possible reduced buechi
	 * automaton.
	 * 
	 * @param result
	 *            The result of the simulation calculation, a possible reduced
	 *            buechi automaton.
	 */
	protected void setResult(final INestedWordAutomatonOldApi<LETTER, STATE> result) {
		m_Result = result;
	}

	/**
	 * Sets the object that is used for computing the SCCs of a given buechi
	 * automaton.
	 * 
	 * @param sccComp
	 *            The object to set.
	 */
	protected void setSccComp(
			final SccComputation<Vertex<LETTER, STATE>, StronglyConnectedComponent<Vertex<LETTER, STATE>>> sccComp) {
		m_SccComp = sccComp;
	}

	/**
	 * Sets if the simulation calculation should be optimized using SCC,
	 * Strongly Connected Components or not.
	 * 
	 * @param useSCCs
	 *            True if the simulation calculation gets optimized by using
	 *            SCC, false if not.
	 */
	protected void setUseSCCs(final boolean useSCCs) {
		m_UseSCCs = useSCCs;
	}

	/**
	 * Calculates the progress measure of a given vertex by trying to increase
	 * it, based on its best neighbor measure and priority.<br/>
	 * If the returned value has increased the vertex can make a better move
	 * than in its previous run and should be updated.
	 * 
	 * @param v
	 *            The vertex to update
	 * @param localInfinity
	 *            The local infinity in the containing SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The containing SCC or <tt>null</tt> if not used
	 * @return The possible increased progress measure
	 */
	protected int update(final Vertex<LETTER, STATE> v, final int localInfinity, final Set<Vertex<LETTER, STATE>> scc) {
		return increaseVector(getGameGraph().getPriority(v), calcBestNghbMeasure(v, localInfinity, scc), localInfinity);
	}
}
