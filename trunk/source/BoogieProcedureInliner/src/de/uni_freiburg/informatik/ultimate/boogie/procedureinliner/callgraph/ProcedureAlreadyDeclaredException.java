package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.Activator;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.CancelToolchainException;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.result.AbstractResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

public class ProcedureAlreadyDeclaredException extends CancelToolchainException {

	private static final long serialVersionUID = 4403766989405696198L;

	public ProcedureAlreadyDeclaredException(Procedure procedure) {
		super("Procedure was already declared: " + procedure.getIdentifier(), procedure.getLocation());
	}
	
	@Override
	protected AbstractResult createResult(String pluginId) {
		return new UnsupportedSyntaxResult<Procedure>(Activator.PLUGIN_ID, getLocation(), getMessage());
	}
}
