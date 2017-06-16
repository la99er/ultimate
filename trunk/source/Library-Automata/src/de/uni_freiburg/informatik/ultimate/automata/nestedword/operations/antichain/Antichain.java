/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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


package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.antichain;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/**
 * @author Yong Li (liyong@ios.ac.cn)
 * */
public class Antichain {
	
	private Map<Integer, Set<StateNCSB>> mPairMap;
	
	public Antichain() {
		mPairMap = new HashMap<>();
	}
	
	/**
	 * return true if @param snd has been added successfully
	 * */
	public boolean addPair(int fst, StateNCSB snd) {
		Set<StateNCSB> sndElem = mPairMap.get(fst);
		if(sndElem == null) {
			sndElem = new HashSet<>();
		}
		//avoid to add pairs are covered by other pairs
		boolean canAdd = true;
		for(StateNCSB state : sndElem) {
			if(snd.coveredBy(state)) { // already covered by other pairs
				canAdd = false;
				break;
			}
		}
		if(canAdd) {
			sndElem.add(snd);
		}
		
		mPairMap.put(fst, sndElem);
		return canAdd;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for(Entry<Integer, Set<StateNCSB>> entry : mPairMap.entrySet()) {
			sb.append(entry.getKey() + " -> " + entry.getValue() + "\n");
		}
		return sb.toString();
	}

}
