/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ICongruenceClosureElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class CcManager<ELEM extends ICongruenceClosureElement<ELEM>> {
	private final IPartialComparator<CongruenceClosure<ELEM>> mCcComparator;

	public CcManager(final IPartialComparator<CongruenceClosure<ELEM>> ccComparator) {
		mCcComparator = ccComparator;
	}

	public CongruenceClosure<ELEM> getMeet(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2) {
		return getMeet(cc1, cc2, null);
	}

	public CongruenceClosure<ELEM> getMeet(final CongruenceClosure<ELEM> cc1,
			final CongruenceClosure<ELEM> cc2, final CongruenceClosure<ELEM>.RemoveElement remInfo) {
		final CongruenceClosure<ELEM> result;
		if (remInfo == null) {
			result = cc1.meetRec(cc2);
		} else {
			result = cc1.meetRec(cc2, remInfo);
		}
		return result;
	}



	public CongruenceClosure<ELEM> getJoin(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2) {
		return cc1.join(cc2);
	}

	public ComparisonResult compare(final CongruenceClosure<ELEM> cc1,
			final CongruenceClosure<ELEM> cc2) {
		return mCcComparator.compare(cc1, cc2);
	}

	/**
	 * The given list is implictly a disjunction.
	 * If one element in the disjunction is stronger than another, we can drop it.
	 *
	 * TODO: poor man's solution, could be done much nicer with lattice representation..
	 *
	 * @param unionList
	 * @return
	 */
	public Set<CongruenceClosure<ELEM>> filterRedundantCcs(final Set<CongruenceClosure<ELEM>> unionList) {
		final PartialOrderCache<CongruenceClosure<ELEM>> poc = new PartialOrderCache<>(mCcComparator);
		return filterRedundantCcs(unionList, poc);
	}

//	public CongruenceClosure<ELEM> getSingleDisequalityCc(final ELEM elem1, final ELEM elem2) {
//		final CongruenceClosure<ELEM> newCC = new CongruenceClosure<>();
//		newCC.reportDisequality(elem1, elem2);
//		return newCC;
//	}

//	public CongruenceClosure<ELEM> getSingleEqualityCc(final ELEM elem1,
//			final ELEM  elem2) {
//		final CongruenceClosure<ELEM> newCC = new CongruenceClosure<>();
//		newCC.reportEquality(elem1, elem2);
//		return newCC;
//	}

	public  IPartialComparator<CongruenceClosure<ELEM>> getCcComparator() {
		return mCcComparator;
	}

	public Set<CongruenceClosure<ELEM>> filterRedundantCcs(final Set<CongruenceClosure<ELEM>> unionList,
			final PartialOrderCache<CongruenceClosure<ELEM>> ccPoCache) {
		return ccPoCache.getMaximalRepresentatives(unionList);
	}

	public CongruenceClosure<ELEM> reportEquality(final ELEM node1, final ELEM node2,
			final CongruenceClosure<ELEM> origCc) {
		final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
		unfrozen.reportEquality(node1, node2);
		unfrozen.freeze();
		return unfrozen;
	}

	public CongruenceClosure<ELEM> reportDisequality(final ELEM node1, final ELEM node2,
			final CongruenceClosure<ELEM> origCc) {
		final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
		unfrozen.reportDisequality(node1, node2);
		unfrozen.freeze();
		return unfrozen;
	}

	public CongruenceClosure<ELEM> transformElementsAndFunctions(final Function<ELEM, ELEM> elemTransformer,
			final CongruenceClosure<ELEM> origCc) {
		final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
		unfrozen.transformElementsAndFunctions(elemTransformer);
		unfrozen.freeze();
		return unfrozen;
	}

	public CongruenceClosure<ELEM> removeSimpleElement(final ELEM elem, final CongruenceClosure<ELEM> origCc) {
		final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
		unfrozen.removeSimpleElement(elem);
		unfrozen.freeze();
		return unfrozen;
	}

	public CongruenceClosure<ELEM> removeSimpleElementDontIntroduceNewNodes(final ELEM elem,
			final CongruenceClosure<ELEM> origCc) {
		final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
		unfrozen.removeSimpleElementDontIntroduceNewNodes(elem);
		unfrozen.freeze();
		return unfrozen;

	}

	public Pair<CongruenceClosure<ELEM>, Set<ELEM>> removeSimpleElementDontUseWeqGpaTrackAddedNodes(final ELEM elem,
			final CongruenceClosure<ELEM> origCc) {
		final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
		final Set<ELEM> addedNodes = unfrozen.removeSimpleElementDontUseWeqGpaTrackAddedNodes(elem);
		unfrozen.freeze();
		return new Pair<>(unfrozen, addedNodes);
	}

	private CongruenceClosure<ELEM> unfreeze(final CongruenceClosure<ELEM> origCc) {
		assert origCc.isFrozen();
		return new CongruenceClosure<>(origCc);
	}
}