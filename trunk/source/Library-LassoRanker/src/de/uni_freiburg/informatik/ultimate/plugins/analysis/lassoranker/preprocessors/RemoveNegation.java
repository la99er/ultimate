/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;


/**
 * Remove negation before atoms.
 * 
 * <ul>
 * <li> NOT (a >= b) becomes a < b
 * <li> NOT (a > b) becomes a <= b
 * </ul>
 * 
 * @author Jan Leike
 */
public class RemoveNegation extends TermTransformer implements PreProcessor {
	private Script m_script;
	
	@Override
	public String getDescription() {
		return "Removes negation before atoms.";
	}

	@Override
	public Term process(Script script, Term term) {
		m_script = script;
		return transform(term);
	}
	
	@Override
	protected void convert(Term term) {
		assert(m_script != null);
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appt = (ApplicationTerm) term;
			if (appt.getFunction().getName().equals("not")) {
				assert(appt.getParameters().length == 1);
				Term param = appt.getParameters()[0];
				assert(param instanceof ApplicationTerm);
				ApplicationTerm appt2 = (ApplicationTerm)param;
				if (appt2.getFunction().getName().equals("<=")) {
					setResult(m_script.term(">", appt2.getParameters()));
				} else if (appt2.getFunction().getName().equals("<")) {
					setResult(m_script.term(">=", appt2.getParameters()));
				} else if (appt2.getFunction().getName().equals(">=")) {
					setResult(m_script.term("<", appt2.getParameters()));
				} else if (appt2.getFunction().getName().equals(">")) {
					setResult(m_script.term("<=", appt2.getParameters()));
				} else {
					assert(false);
				}
				return;
			}
		}
		super.convert(term);
	}
}
