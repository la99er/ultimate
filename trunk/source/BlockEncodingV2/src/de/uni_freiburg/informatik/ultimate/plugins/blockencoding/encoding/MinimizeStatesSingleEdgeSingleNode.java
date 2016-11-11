/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding;

import java.util.Collection;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Least aggressive minimization (besides no attempt). Tries to remove states that have only one incoming and one
 * outgoing edge.
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class MinimizeStatesSingleEdgeSingleNode extends BaseMinimizeStates {
	
	public MinimizeStatesSingleEdgeSingleNode(final BoogieIcfgContainer icfg,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final BlockEncodingBacktranslator backtranslator,
			final Predicate<IcfgLocation> funIsAccepting) {
		super(icfg, services, backtranslator, simplificationTechnique, xnfConversionTechnique, funIsAccepting);
	}
	
	@Override
	protected Collection<? extends IcfgLocation> processCandidate(final BoogieIcfgContainer icfg,
			final IcfgLocation target, final Set<IcfgLocation> closed) {
		
		if (target.getIncomingEdges().size() != 1 || target.getOutgoingEdges().size() != 1) {
			return target.getOutgoingNodes();
		}
		
		// this node has exactly one incoming and one outgoing edge,
		// so we have the two edges
		// e1 = (q1,st1,q2)
		// e2 = (q2,st2,q3)
		final IcfgEdge predEdge = target.getIncomingEdges().get(0);
		final IcfgEdge succEdge = target.getOutgoingEdges().get(0);
		
		final BoogieIcfgLocation pred = (BoogieIcfgLocation) predEdge.getSource();
		final BoogieIcfgLocation succ = (BoogieIcfgLocation) succEdge.getTarget();
		
		if (!isNotNecessary(target) && !isOneNecessary(pred, succ)) {
			// the nodes do not fulfill the conditions, return
			return target.getOutgoingNodes();
		}
		
		if (!isCombinableEdgePair(predEdge, succEdge)) {
			// the edges do not fulfill the conditions, return
			return target.getOutgoingNodes();
		}
		
		// all conditions are met so we can start with creating new edges
		// we delete e1 and e2 and q2 and add the new edge (q1,st1;st2,q3)
		
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    will remove " + target.getDebugIdentifier());
		}
		
		predEdge.disconnectSource();
		predEdge.disconnectTarget();
		succEdge.disconnectSource();
		succEdge.disconnectTarget();
		mRemovedEdges += 2;
		
		getEdgeBuilder().constructSequentialComposition(pred, succ, (CodeBlock) predEdge, (CodeBlock) succEdge);
		
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    removed 2, added 2 edges");
		}
		// we added new edges to pred, we have to recheck them now
		return pred.getOutgoingNodes();
		
	}
}