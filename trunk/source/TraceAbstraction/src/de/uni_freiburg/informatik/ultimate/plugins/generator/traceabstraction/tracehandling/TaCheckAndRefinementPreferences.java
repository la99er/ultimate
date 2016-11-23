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

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.InterpolantAutomatonBuilderFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;

/**
 * Wrapper for preferences of trace check and refinement selection module.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class TaCheckAndRefinementPreferences {
	// fields that are provided in the constructor
	private final InterpolationTechnique mInterpolationTechnique;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final PredicateFactory mPredicateFactory;
	private final BoogieIcfgContainer mIcfgContainer;
	private final IToolchainStorage mToolchainStorage;
	private final InterpolantAutomatonBuilderFactory mInterpolantAutomatonBuilderFactory;
	private final CegarLoopStatisticsGenerator mCegarLoopBenchmark;
	private final int mIteration;
	
	// fields that can be read from the TAPreferences
	private final boolean mUseSeparateSolverForTracechecks;
	private final SolverMode mSolverMode;
	private final boolean mFakeNonIncrementalSolver;
	private final String mCommandExternalSolver;
	private final boolean mDumpSmtScriptToFile;
	private final String mPathOfDumpedScript;
	private final String mLogicForExternalSolver;
	
	// fields that can be read from the IUltimateServiceProvider
	private final AssertCodeBlockOrder mAssertCodeBlocksIncrementally;
	private final UnsatCores mUnsatCores;
	private final boolean mUseLiveVariables;
	private final boolean mUseInterpolantConsolidation;
	private final boolean mUseNonlinearConstraints;
	private final boolean mUseVarsFromUnsatCore;
	
	/**
	 * Constructor from existing trace abstraction and Ultimate preferences.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param taPrefs
	 *            trace abstraction preferences
	 * @param interpolationTechnique
	 *            interpolation technique
	 * @param iteration
	 *            iteration number
	 * @param icfgContainer
	 *            ICFG container
	 * @param simplificationTechnique
	 *            simplification technique
	 * @param xnfConversionTechnique
	 *            XNF conversion technique
	 * @param cfgSmtToolkit
	 *            CFG-SMT toolkit
	 * @param predicateFactory
	 *            predicate factory
	 * @param toolchainStorage
	 *            toolchain storage
	 * @param interpolantAutomatonBuilderFactory
	 *            factory for interpolant automaton builder
	 * @param cegarLoopBenchmark
	 *            benchmark object of the CEGAR loop
	 */
	public TaCheckAndRefinementPreferences(final IUltimateServiceProvider services, final TAPreferences taPrefs,
			final InterpolationTechnique interpolationTechnique, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final CfgSmtToolkit cfgSmtToolkit,
			final PredicateFactory predicateFactory, final BoogieIcfgContainer icfgContainer,
			final IToolchainStorage toolchainStorage,
			final InterpolantAutomatonBuilderFactory interpolantAutomatonBuilderFactory,
			final CegarLoopStatisticsGenerator cegarLoopBenchmark, final int iteration) {
		mInterpolationTechnique = interpolationTechnique;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mCfgSmtToolkit = cfgSmtToolkit;
		mPredicateFactory = predicateFactory;
		mIcfgContainer = icfgContainer;
		mToolchainStorage = toolchainStorage;
		mInterpolantAutomatonBuilderFactory = interpolantAutomatonBuilderFactory;
		mCegarLoopBenchmark = cegarLoopBenchmark;
		mIteration = iteration;
		
		mUseSeparateSolverForTracechecks = taPrefs.useSeparateSolverForTracechecks();
		mSolverMode = taPrefs.solverMode();
		mFakeNonIncrementalSolver = taPrefs.fakeNonIncrementalSolver();
		mCommandExternalSolver = taPrefs.commandExternalSolver();
		mDumpSmtScriptToFile = taPrefs.dumpSmtScriptToFile();
		mPathOfDumpedScript = taPrefs.pathOfDumpedScript();
		mLogicForExternalSolver = taPrefs.logicForExternalSolver();
		
		final IPreferenceProvider ultimatePrefs = services.getPreferenceProvider(Activator.PLUGIN_ID);
		mAssertCodeBlocksIncrementally =
				ultimatePrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ASSERT_CODEBLOCKS_INCREMENTALLY,
						AssertCodeBlockOrder.class);
		mUnsatCores = ultimatePrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_UNSAT_CORES, UnsatCores.class);
		mUseLiveVariables = ultimatePrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_LIVE_VARIABLES);
		mUseInterpolantConsolidation =
				ultimatePrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANTS_CONSOLIDATION);
		mUseNonlinearConstraints = ultimatePrefs
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_NONLINEAR_CONSTRAINTS_IN_PATHINVARIANTS);
		mUseVarsFromUnsatCore =
				ultimatePrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_UNSAT_CORES_IN_PATHINVARIANTS);
	}
	
	public boolean getUseSeparateSolverForTracechecks() {
		return mUseSeparateSolverForTracechecks;
	}
	
	public SolverMode getSolverMode() {
		return mSolverMode;
	}
	
	public boolean getFakeNonIncrementalSolver() {
		return mFakeNonIncrementalSolver;
	}
	
	public String getCommandExternalSolver() {
		return mCommandExternalSolver;
	}
	
	public boolean getDumpSmtScriptToFile() {
		return mDumpSmtScriptToFile;
	}
	
	public String getPathOfDumpedScript() {
		return mPathOfDumpedScript;
	}
	
	public String getLogicForExternalSolver() {
		return mLogicForExternalSolver;
	}
	
	public InterpolationTechnique getInterpolationTechnique() {
		return mInterpolationTechnique;
	}
	
	public SimplificationTechnique getSimplificationTechnique() {
		return mSimplificationTechnique;
	}
	
	public XnfConversionTechnique getXnfConversionTechnique() {
		return mXnfConversionTechnique;
	}
	
	public CfgSmtToolkit getCfgSmtToolkit() {
		return mCfgSmtToolkit;
	}
	
	public PredicateFactory getPredicateFactory() {
		return mPredicateFactory;
	}
	
	public BoogieIcfgContainer getIcfgContainer() {
		return mIcfgContainer;
	}
	
	public IToolchainStorage getToolchainStorage() {
		return mToolchainStorage;
	}

	public InterpolantAutomatonBuilderFactory getInterpolantAutomatonBuilderFactory() {
		return mInterpolantAutomatonBuilderFactory;
	}
	
	public CegarLoopStatisticsGenerator getCegarLoopBenchmark() {
		return mCegarLoopBenchmark;
	}
	
	public int getIteration() {
		return mIteration;
	}
	
	public AssertCodeBlockOrder getAssertCodeBlocksIncrementally() {
		return mAssertCodeBlocksIncrementally;
	}
	
	public UnsatCores getUnsatCores() {
		return mUnsatCores;
	}
	
	public boolean getUseLiveVariables() {
		return mUseLiveVariables;
	}
	
	public boolean getUseInterpolantConsolidation() {
		return mUseInterpolantConsolidation;
	}
	
	public boolean getUseNonlinearConstraints() {
		return mUseNonlinearConstraints;
	}
	
	public boolean getUseVarsFromUnsatCore() {
		return mUseVarsFromUnsatCore;
	}
}