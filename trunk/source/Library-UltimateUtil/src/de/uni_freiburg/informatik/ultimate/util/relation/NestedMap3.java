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
package de.uni_freiburg.informatik.ultimate.util.relation;

import java.util.HashMap;
import java.util.Map;

/**
 * TODO: comment
 * @author Matthias Heizmann
 *
 * @param <K1>
 * @param <K2>
 * @param <K3>
 * @param <V>
 */
public class NestedMap3<K1, K2, K3, V> {
	
	private final Map<K1, NestedMap2<K2, K3, V>> m_K1ToK2ToK3V = 
			new HashMap<K1, NestedMap2<K2, K3, V>>();
	
	public V put(K1 key1, K2 key2, K3 key3, V value) {
		NestedMap2<K2, K3, V> k2tok3toV = m_K1ToK2ToK3V.get(key1);
		if (k2tok3toV == null) {
			k2tok3toV = new NestedMap2<>();
			m_K1ToK2ToK3V.put(key1, k2tok3toV);
		}
		return k2tok3toV.put(key2, key3, value);
	}
	
	public V get(K1 key1, K2 key2, K3 key3) {
		NestedMap2<K2, K3, V> k2tok3toV = m_K1ToK2ToK3V.get(key1);
		if (k2tok3toV == null) {
			return null;
		} else {
			return k2tok3toV.get(key2, key3);
		}
	}
}
