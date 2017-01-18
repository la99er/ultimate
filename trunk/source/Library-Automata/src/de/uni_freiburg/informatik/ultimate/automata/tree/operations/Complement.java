package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;

/**
 *  Complements a given treeAutomaton.
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER> letter of the tree automaton.
 * @param <STATE> state of the tree automaton.
 */
public class Complement<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final ITreeAutomatonBU<LETTER, STATE> treeAutomaton;
	private final IStateFactory<STATE> stateFactory;
	
	protected final ITreeAutomatonBU<LETTER, STATE> result;
	
	public Complement(final ITreeAutomatonBU<LETTER, STATE> tree, final IStateFactory<STATE> factory) {
		treeAutomaton = tree;
		stateFactory = factory;
		
		result = computeResult();
	}
	@Override
	public String operationName() {
		return "Complement";
	}

	@Override
	public String startMessage() {
		return "Starting complementing";
	}

	@Override
	public String exitMessage() {
		return "Exiting complementing";
	}
	
	private ITreeAutomatonBU<LETTER, STATE> computeResult() {
		final Determinize<LETTER, STATE> op = new Determinize<>(treeAutomaton, stateFactory);
		final TreeAutomatonBU<LETTER, STATE> res = (TreeAutomatonBU<LETTER, STATE>) op.getResult();
		res.complementFinals();
		final Minimize<LETTER, STATE> mini = new Minimize<>(res, stateFactory);
		return mini.getResult();
	}
	
	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return result;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}
	
	public static void main(String[] args) throws AutomataLibraryException {
		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
		final TreeAutomatonBU<String, String> treeB = new TreeAutomatonBU<>();
		
		final String NAT = "NAT", NatList = "NatList", Bool = "Bool", BoolList = "BoolList", initA = "_", initB = "_";
		treeA.addInitialState(initA);
		treeA.addFinalState(NatList);
		treeA.addRule("0", new ArrayList<>(Arrays.asList(new String[]{initA})), NAT);
		treeA.addRule("s", new ArrayList<>(Arrays.asList(new String[]{NAT})), NAT);
		treeA.addRule("nil", new ArrayList<>(Arrays.asList(new String[]{initA})), NatList);
		treeA.addRule("cons", new ArrayList<>(Arrays.asList(new String[]{NAT, NatList})), NatList);
		
		
		treeB.addInitialState(initB);
		treeB.addFinalState(BoolList);
		treeB.addRule("0", new ArrayList<>(Arrays.asList(new String[]{initB})), Bool);
		treeB.addRule("1", new ArrayList<>(Arrays.asList(new String[]{initB})), Bool);
		treeB.addRule("nil", new ArrayList<>(Arrays.asList(new String[]{initB})), BoolList);
		treeB.addRule("cons", new ArrayList<>(Arrays.asList(new String[]{Bool, BoolList})), BoolList);

		final StringFactory fac = new StringFactory();
		final Complement<String, String> com = new Complement<>(treeB, fac);
		
		final Intersect<String, String> op = new Intersect<>(treeA, com.getResult(), fac);
		final ITreeAutomatonBU<String, String> res = op.getResult();
		
		System.out.println(treeA.toString() + "\n");
		System.out.println(treeB.toString() + "\n");
		System.out.println(com.getResult() + "\n");
		System.out.println(res + "\n");
		System.out.println(((TreeAutomatonBU<String, String>) res).DebugString() + "\n");
	}
}
