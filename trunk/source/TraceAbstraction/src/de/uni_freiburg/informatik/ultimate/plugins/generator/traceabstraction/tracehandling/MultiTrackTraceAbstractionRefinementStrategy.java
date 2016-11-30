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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.MultiTrackInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

/**
 * {@link IRefinementStrategy} that first tries a {@link InterpolatingTraceChecker} using
 * {@link InterpolationTechnique#Craig_TreeInterpolation} and then {@link InterpolationTechnique#FPandBP}.
 * <p>
 * The class uses a {@link MultiTrackInterpolantAutomatonBuilder} for constructing the interpolant automaton.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class MultiTrackTraceAbstractionRefinementStrategy implements IRefinementStrategy {
	private static final String Z3_COMMAND = "z3 -smt2 -in SMTLIB2_COMPLIANT=true";
	
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences mPrefs;
	private final IRun<CodeBlock, IPredicate, ?> mCounterexample;
	private final IAutomaton<CodeBlock, IPredicate> mAbstraction;
	private final PredicateUnifier mPredicateUnifier;
	
	// TODO Christian 2016-11-11: Matthias wants to get rid of this
	private final TAPreferences mTaPrefsForInterpolantConsolidation;
	
	private final Iterator<InterpolationTechnique> mInterpolationTechniques;
	
	private TraceCheckerConstructor mTcConstructorFromPrefs;
	private TraceChecker mTraceChecker;
	private IInterpolantGenerator mInterpolantGenerator;
	private IInterpolantAutomatonBuilder<CodeBlock, IPredicate> mInterpolantAutomatonBuilder;
	
	/**
	 * @param prefs
	 *            Preferences. pending contexts
	 * @param managedScript
	 *            managed script
	 * @param services
	 *            Ultimate services
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param counterexample
	 *            counterexample trace
	 * @param logger
	 *            logger
	 * @param abstraction
	 *            abstraction
	 * @param taPrefsForInterpolantConsolidation
	 *            temporary argument, should be removed
	 */
	public MultiTrackTraceAbstractionRefinementStrategy(final ILogger logger,
			final TaCheckAndRefinementPreferences prefs, final IUltimateServiceProvider services,
			final PredicateUnifier predicateUnifier, final IRun<CodeBlock, IPredicate, ?> counterexample,
			final IAutomaton<CodeBlock, IPredicate> abstraction,
			final TAPreferences taPrefsForInterpolantConsolidation) {
		mServices = services;
		mLogger = logger;
		mPrefs = prefs;
		mCounterexample = counterexample;
		mAbstraction = abstraction;
		mPredicateUnifier = predicateUnifier;
		mTaPrefsForInterpolantConsolidation = taPrefsForInterpolantConsolidation;
		
		mInterpolationTechniques = initializeInterpolationTechniquesList();
		
		// dummy construction, is overwritten in the next step
		mTcConstructorFromPrefs =
				new TraceCheckerConstructor(mPrefs, null, mServices, mPredicateUnifier, mCounterexample, null);
		mTcConstructorFromPrefs = constructTraceCheckerConstructor();
	}
	
	@Override
	public boolean hasNext(final RefinementStrategyAdvance advance) {
		switch (advance) {
			case TRACE_CHECKER:
				return mInterpolationTechniques.hasNext();
			case INTERPOLANT_GENERATOR:
				if (mInterpolantGenerator instanceof TraceCheckerSpWpWrapper) {
					// several interpolant sequences possible here
					return ((TraceCheckerSpWpWrapper) mInterpolantGenerator).hasNext();
				}
				return false;
			default:
				throw new IllegalArgumentException("Unknown mode: " + advance);
		}
	}
	
	@Override
	public void next(final RefinementStrategyAdvance advance) {
		switch (advance) {
			case TRACE_CHECKER:
				mTcConstructorFromPrefs = constructTraceCheckerConstructor();
				break;
			case INTERPOLANT_GENERATOR:
				// TODO should we advance the trace checker as well?
				if (mInterpolantGenerator instanceof TraceCheckerSpWpWrapper) {
					// several interpolant sequences possible here
					((TraceCheckerSpWpWrapper) mInterpolantGenerator).next();
				}
				throw new NoSuchElementException();
			default:
				throw new IllegalArgumentException("Unknown mode: " + advance);
		}
	}
	
	@Override
	public TraceChecker getTraceChecker() {
		if (mTraceChecker == null) {
			mTraceChecker = mTcConstructorFromPrefs.get();
		}
		return mTraceChecker;
	}
	
	@Override
	public IInterpolantGenerator getInterpolantGenerator() {
		if (mInterpolantGenerator == null) {
			mInterpolantGenerator = constructInterpolantGenerator(getTraceChecker());
		}
		return mInterpolantGenerator;
	}
	
	@Override
	public IInterpolantAutomatonBuilder<CodeBlock, IPredicate>
			getInterpolantAutomatonBuilder(final List<InterpolantsPreconditionPostcondition> ipps) {
		if (mInterpolantAutomatonBuilder == null) {
			mInterpolantAutomatonBuilder =
					new MultiTrackInterpolantAutomatonBuilder(mServices, mCounterexample, ipps, mAbstraction);
		}
		return mInterpolantAutomatonBuilder;
	}
	
	private static Iterator<InterpolationTechnique> initializeInterpolationTechniquesList() {
		final List<InterpolationTechnique> list = new ArrayList<>(2);
		list.add(InterpolationTechnique.Craig_TreeInterpolation);
		list.add(InterpolationTechnique.FPandBP);
		return list.iterator();
	}
	
	private TraceCheckerConstructor constructTraceCheckerConstructor() {
		// reset trace checker
		mTraceChecker = null;
		
		final InterpolationTechnique nextTechnique = mInterpolationTechniques.next();
		final ManagedScript managedScript = constructManagedScript(nextTechnique);
		
		return new TraceCheckerConstructor(mTcConstructorFromPrefs, managedScript, nextTechnique);
	}
	
	private ManagedScript constructManagedScript(final InterpolationTechnique interpolationTechnique) {
		final Settings solverSettings;
		switch (interpolationTechnique) {
			case Craig_TreeInterpolation:
				solverSettings = new Settings(false, false, null, 10_000, null, false, null, null);
				break;
			case FPandBP:
				// final String commandExternalSolver = RcfgPreferenceInitializer.Z3_DEFAULT;
				final String commandExternalSolver = Z3_COMMAND;
				solverSettings = new Settings(false, true, commandExternalSolver, 0, null, false, null, null);
				break;
			default:
				throw new IllegalArgumentException(
						"Managed script construction not supported for interpolation technique: "
								+ interpolationTechnique);
		}
		final Script solver = SolverBuilder.buildAndInitializeSolver(mServices, mPrefs.getToolchainStorage(),
				mPrefs.getSolverMode(), solverSettings, false, false, mPrefs.getLogicForExternalSolver(),
				"TraceCheck_Iteration" + mPrefs.getIteration());
		final ManagedScript result = new ManagedScript(mServices, solver);
		
		// TODO do we need this?
		final TermTransferrer tt = new TermTransferrer(solver);
		for (final Term axiom : mPrefs.getIcfgContainer().getBoogie2SMT().getAxioms()) {
			solver.assertTerm(tt.transform(axiom));
		}
		
		return result;
	}
	
	/**
	 * TODO Refactor this code duplicate with {@link FixedTraceAbstractionRefinementStrategy}. But careful: The
	 * {@link TraceCheckerSpWpWrapper} code is unique to this class.
	 */
	private IInterpolantGenerator constructInterpolantGenerator(final TraceChecker tracechecker) {
		final TraceChecker localTraceChecker = Objects.requireNonNull(tracechecker,
				"cannot construct interpolant generator if no trace checker is present");
		if (localTraceChecker instanceof InterpolatingTraceChecker) {
			if (localTraceChecker instanceof TraceCheckerSpWp) {
				return new TraceCheckerSpWpWrapper((TraceCheckerSpWp) localTraceChecker);
			}
			final InterpolatingTraceChecker interpolatingTraceChecker = (InterpolatingTraceChecker) localTraceChecker;
			
			if (mPrefs.getUseInterpolantConsolidation()) {
				try {
					return consolidateInterpolants(interpolatingTraceChecker);
				} catch (final AutomataOperationCanceledException e) {
					// Timeout
					throw new AssertionError("react on timeout, not yet implemented");
				}
			}
			return interpolatingTraceChecker;
		}
		// TODO insert code here to support generating interpolants from a different source
		throw new AssertionError("Currently only interpolating trace checkers are supported.");
	}
	
	/**
	 * TODO Refactor this code duplicate with {@link FixedTraceAbstractionRefinementStrategy}.
	 */
	private IInterpolantGenerator consolidateInterpolants(final InterpolatingTraceChecker interpolatingTraceChecker)
			throws AutomataOperationCanceledException {
		final CfgSmtToolkit cfgSmtToolkit = mPrefs.getCfgSmtToolkit();
		final InterpolantConsolidation interpConsoli = new InterpolantConsolidation(
				mPredicateUnifier.getTruePredicate(), mPredicateUnifier.getFalsePredicate(),
				new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(mCounterexample.getWord()), cfgSmtToolkit,
				cfgSmtToolkit.getModifiableGlobalsTable(), mServices, mLogger, mPredicateUnifier,
				interpolatingTraceChecker, mTaPrefsForInterpolantConsolidation);
		// Add benchmark data of interpolant consolidation
		mPrefs.getCegarLoopBenchmark()
				.addInterpolationConsolidationData(interpConsoli.getInterpolantConsolidationBenchmarks());
		return interpConsoli;
	}
}