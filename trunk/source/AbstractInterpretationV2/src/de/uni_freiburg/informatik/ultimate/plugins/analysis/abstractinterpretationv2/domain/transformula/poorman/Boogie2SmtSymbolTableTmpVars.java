/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * Wraps the default symbol table variable provider to allow to add variables temporarily to the symbol table. This is
 * used in abstract interpretation only.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class Boogie2SmtSymbolTableTmpVars implements IBoogieSymbolTableVariableProvider {

	private final Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;
	private final Map<String, BoogieVar> mTempVars;

	public Boogie2SmtSymbolTableTmpVars(final Boogie2SmtSymbolTable boogie2SmtSymbolTable) {
		mBoogie2SmtSymbolTable = boogie2SmtSymbolTable;
		mTempVars = new HashMap<>();
	}

	/**
	 * Adds a new temporary variable to the symbol table. Throws an exception if the variable is already present.
	 *
	 * @param var
	 *            The variable to add.
	 */
	public void addTemporaryVariable(final BoogieVar var) {
		if (mTempVars.put(var.getGloballyUniqueId(), var) != null) {
			throw new UnsupportedOperationException(
					"Temporary variable " + var.getGloballyUniqueId() + " already present.");
		}
	}

	/**
	 * Removes a temporary variable from the symbol table. Throws an exception if the variable is not found.
	 *
	 * @param var
	 *            The variable to remove.
	 */
	public void removeTemporaryVariable(final BoogieVar var) {
		if (mTempVars.remove(var.getGloballyUniqueId()) == null) {
			throw new UnsupportedOperationException(
					"Variable " + var.getGloballyUniqueId() + " not present in temporary variables.");
		}
	}

	@Override
	public IProgramVar getBoogieVar(final String varId, final DeclarationInformation declarationInformation,
			final boolean inOldContext) {
		if (mTempVars.containsKey(varId)) {
			return mTempVars.get(varId);
		}

		return mBoogie2SmtSymbolTable.getBoogieVar(varId, declarationInformation, inOldContext);
	}

	@Override
	public IProgramVar getBoogieVar(final String varId, final String procedure, final boolean isInParam) {
		if (mTempVars.containsKey(varId)) {
			return mTempVars.get(varId);
		}

		return mBoogie2SmtSymbolTable.getBoogieVar(varId, procedure, isInParam);
	}

	@Override
	public BoogieConst getBoogieConst(final String constId) {
		return mBoogie2SmtSymbolTable.getBoogieConst(constId);
	}

	public int getNumberOfTempVars() {
		return mTempVars.size();
	}

}
