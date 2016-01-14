/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Holds all numbered literals in the program.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class LiteralCollection {

	private final List<BigDecimal> mSortedNumbersSet;

	protected LiteralCollection(Set<BigDecimal> realsSet) {
		mSortedNumbersSet = realsSet.stream().sorted().collect(Collectors.toList());
	}

	public BigDecimal getNextIntegerPositive(BigDecimal value) {

		final BigDecimal nextNumber = getNextNumberPositive(value);

		if (nextNumber == null) {
			return null;
		}

		return nextNumber.setScale(0, RoundingMode.UP);
	}

	public BigDecimal getNextIntegerNegative(BigDecimal value) {

		final BigDecimal nextNumber = getNextIntegerNegative(value);

		if (nextNumber == null) {
			return null;
		}

		return nextNumber.setScale(0, RoundingMode.UP);
	}

	public BigDecimal getNextRealPositive(BigDecimal value) {
		return getNextNumberPositive(value);
	}

	public BigDecimal getNextRealNegative(BigDecimal value) {
		return getNextNumberNegative(value);
	}

	private BigDecimal getNextNumberPositive(BigDecimal value) {
		ListIterator<BigDecimal> it = mSortedNumbersSet.listIterator();

		while (it.hasNext()) {
			final BigDecimal current = it.next();
			if (current.compareTo(value) > 0) {
				return current;
			}
		}

		// There is no element in the list which is smaller than the given value.
		return null;
	}

	private BigDecimal getNextNumberNegative(BigDecimal value) {
		ListIterator<BigDecimal> it = mSortedNumbersSet.listIterator(mSortedNumbersSet.size());

		while (it.hasPrevious()) {
			final BigDecimal current = it.previous();
			if (current.compareTo(value) < 0) {
				return current;
			}
		}

		// There is no element in the list which is smaller than the given value.
		return null;
	}
}
