/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Provides static methods for {@link IProgramVar}s.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ProgramVarUtils {
	
	private ProgramVarUtils() {
		
	}

	
	/**
	 * Construct primed constant for a {@link IProgramVar}
	 * @param script {@link ManagedScript} for which constant is constructed.
	 * @param lockOwner Object that currently locks the {@link ManagedScript}.
	 */
	public static ApplicationTerm constructPrimedConstant(final ManagedScript script, final Object lockOwner, final Sort sort, final String name) {
		ApplicationTerm primedConstant;
		{
			final String primedConstantName = "c_" + name + "_primed";
			script.declareFun(lockOwner, primedConstantName, new Sort[0], sort);
			primedConstant = (ApplicationTerm) script.term(lockOwner, primedConstantName);
		}
		return primedConstant;
	}

	/**
	 * Construct default constant for a {@link IProgramVar}
	 * (The default constant is used in {@link IPredicate}s and as unprimed
	 * instance of variables in {@link TransFormula}s
	 * @param script {@link ManagedScript} for which constant is constructed.
	 * @param lockOwner Object that currently locks the {@link ManagedScript}.
	 */
	public static ApplicationTerm constructDefaultConstant(final ManagedScript script, final Object lockOwner, final Sort sort, final String name) {
		ApplicationTerm defaultConstant;
		{
			final String defaultConstantName = "c_" + name;
			script.declareFun(lockOwner, defaultConstantName, new Sort[0], sort);
			defaultConstant = (ApplicationTerm) script.term(lockOwner, defaultConstantName);
		}
		return defaultConstant;
	}
	
	
	public static Set<IProgramNonOldVar> extractNonOldVars(final Term term, final IIcfgSymbolTable symbolTable) {
		final Set<IProgramNonOldVar> result = new HashSet<>();
		for (final TermVariable tv : term.getFreeVars()) {
			final IProgramVar pv = symbolTable.getProgramVar(tv);
			if (pv instanceof IProgramNonOldVar) {
				result.add((IProgramNonOldVar) pv);
			}
		}
		return result;
	}
	
	public static Set<IProgramOldVar> extractOldVars(final Term term, final IIcfgSymbolTable symbolTable) {
		final Set<IProgramOldVar> result = new HashSet<>();
		for (final TermVariable tv : term.getFreeVars()) {
			final IProgramVar pv = symbolTable.getProgramVar(tv);
			if (pv instanceof IProgramOldVar) {
				result.add((IProgramOldVar) pv);
			}
		}
		return result;
	}
	
	public static Term renameNonOldGlobalsToOldGlobals(final Term term, 
			final IIcfgSymbolTable symbolTable,
			final ManagedScript mgdScript) {
		final Set<IProgramNonOldVar> nonOldVars = extractNonOldVars(term, symbolTable);
		final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		for (final IProgramNonOldVar pv : nonOldVars) {
			if (pv instanceof IProgramNonOldVar) {
				final IProgramOldVar oldVar = pv.getOldVar();
				substitutionMapping.put(pv.getTermVariable(), oldVar.getTermVariable());
			}
		}
		final Term result = (new Substitution(mgdScript, substitutionMapping)).transform(term);
		return result;
	}
	
	public static Term renameOldGlobalsToNonOldGlobals(final Term term, 
			final IIcfgSymbolTable symbolTable,
			final ManagedScript mgdScript) {
		final Set<IProgramOldVar> oldVars = extractOldVars(term, symbolTable);
		final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		for (final IProgramOldVar pv : oldVars) {
			if (pv instanceof IProgramOldVar) {
				final IProgramNonOldVar nonoldVar = pv.getNonOldVar();
				substitutionMapping.put(pv.getTermVariable(), nonoldVar.getTermVariable());
			}
		}
		final Term result = (new Substitution(mgdScript, substitutionMapping)).transform(term);
		return result;
	}
	
}