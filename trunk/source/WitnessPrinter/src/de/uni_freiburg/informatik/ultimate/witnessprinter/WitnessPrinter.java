/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE WitnessPrinter plug-in.
 * 
 * The ULTIMATE WitnessPrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE WitnessPrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessPrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessPrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE WitnessPrinter plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessprinter;

import java.io.IOException;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.witnessprinter.preferences.PreferenceInitializer;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class WitnessPrinter implements IOutput {

	private enum Mode {
		TRUE_WITNESS, FALSE_WITNESS, NO_WITNESS
	}

	private Logger mLogger;
	private IUltimateServiceProvider mServices;
	private IToolchainStorage mStorage;
	private Mode mMode;

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.ALL;
	}

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public void setInputDefinition(final GraphType graphType) {

	}

	@Override
	public List<IObserver> getObservers() {
		if (mMode == Mode.TRUE_WITNESS) {
			return Collections.singletonList(new TrueWitnessGenerator(mServices));
		}
		return Collections.emptyList();
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage storage) {
		mStorage = storage;
	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init() {
		mMode = Mode.NO_WITNESS;
		if (!new UltimatePreferenceStore(Activator.PLUGIN_ID).getBoolean(PreferenceInitializer.LABEL_WITNESS_GEN)) {
			mLogger.info("Witness generation is disabled");
			return;
		}

		// determine if there are true or false witnesses
		final Map<String, List<IResult>> results = mServices.getResultService().getResults();
		if (CoreUtil.filterResults(results, CounterExampleResult.class).size() > 0) {
			mLogger.info("Generating witness for counterexample");
			mMode = Mode.FALSE_WITNESS;
		} else if (CoreUtil.filterResults(results, AllSpecificationsHoldResult.class).size() > 0) {
			mLogger.info("Generating witness for proof");
			mMode = Mode.TRUE_WITNESS;
		}
	}

	@Override
	public void finish() {
		if (mMode == Mode.FALSE_WITNESS) {
			final WitnessManager cexVerifier = new WitnessManager(mLogger, mServices, mStorage);
			try {
				cexVerifier.run();
			} catch (IOException | InterruptedException e) {
				throw new RuntimeException(e);
			}
		}
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}
}
