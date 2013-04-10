package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URISyntaxException;
import java.net.URL;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.preferences.PreferenceConstants;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.ILocation;

import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AssignmentExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.BreakStatement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ConditionalBooleanExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ConditionalBooleanOperator;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ConstantExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ContinueStatement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ForStatement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.IfElseStatement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.IfStatement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.NestedLassoword;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.Nestedword;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.OperationInvocationExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.RelationalExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.StatementList;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.VariableExpression;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.WhileStatement;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult.Severity;


enum Flow {
	NORMAL, BREAK, CONTINUE, RETURN;
}
public class TestFileInterpreter {
	
	private static String UNKNOWN_OPERATION = "UNKNOWN_OPERATION";
	
	class AutomataScriptTypeChecker {
		
		public void checkType(AtsASTNode n) throws IllegalArgumentException {
			if (n instanceof AssignmentExpression) {
				checkType((AssignmentExpression) n);
			} else if (n instanceof BinaryExpression) {
				checkType((BinaryExpression) n);
			}  else if (n instanceof ConditionalBooleanExpression) {
				checkType((ConditionalBooleanExpression) n);
			} else if (n instanceof ForStatement) {
				checkType((ForStatement) n);
			} else if (n instanceof IfElseStatement) {
				checkType((IfElseStatement) n);
			} else if (n instanceof IfStatement) {
				checkType((IfStatement) n);
			} else if (n instanceof OperationInvocationExpression) {
				// TODO: Check type of parameters for this operation
			} else if (n instanceof RelationalExpression) {
				checkType((RelationalExpression) n);
			} else if (n instanceof StatementList) {
				for (AtsASTNode stmt : ((StatementList)n).getOutgoingNodes()) {
					checkType(stmt);
				}
			} else if (n instanceof UnaryExpression) {
				checkType((UnaryExpression) n);
			} else if (n instanceof VariableDeclaration) {
				checkType((VariableDeclaration) n);
			} else if (n instanceof WhileStatement) {
				checkType((WhileStatement) n);
			}
				
		}
		
		private void checkType(AssignmentExpression as) throws IllegalArgumentException {
			List<AtsASTNode> children = as.getOutgoingNodes();
			if (children.size() != 2) {
				String message = as.getLocation().getStartLine() + ": AssignmentExpression: It should have 2 operands\n";
				message = message.concat("On the left-hand side there  must be a VariableExpression, ");
				message = message.concat("On the right-hand side there can be an arbitrary expression.");
				throw new IllegalArgumentException(message);
			}
			VariableExpression var = (VariableExpression) children.get(0);
			// Check the type of children
			checkType(children.get(1));
			for (Class<?> c : getTypes(children.get(1))) {
				// Check for correct types
				if (var.isTypeCorrect(c)) {
					return;
				}
			}
			String message = "AssignmentExpression: Type error";
			message = message.concat(children.get(1).getReturnType() + " is not assignable to " + var.getReturnType());
			throw new IllegalArgumentException(message);
			
		}
		
		private void checkType(BinaryExpression be)  throws IllegalArgumentException {
			List<AtsASTNode> children = be.getOutgoingNodes();
			if (children.size() != 2) {
				String message = be.getLocation().getStartLine() + ": BinaryExpression should always have 2 children!\nNum of children: " + children.size();
				throw new IllegalArgumentException(message);
			}
			// Check children for correct type
			checkType(children.get(0));
			checkType(children.get(1));
			
			// Check type of the 1st children
			boolean firstChildHasCorrectType = false;
			for (Class<?> c : getTypes(children.get(0))) {
				if (be.isTypeCorrect(c)) {
					firstChildHasCorrectType = true;
				}
			}
			if(!firstChildHasCorrectType) {
				String message = be.getLocation().getStartLine() + ": BinaryExpression: Left operand \n";
				message = message.concat("Expected: " + be.getReturnType() + "\tGot: " + children.get(0).getReturnType());
				throw new IllegalArgumentException(message);
			}
			
			// Check type of the 2nd children
			for (Class<?> c : getTypes(children.get(1))) {
				if (be.isTypeCorrect(c)) {
					return;
				}
			}
			String message = be.getLocation().getStartLine() + ": BinaryExpression: Right operand\n";
			message = message.concat("Expected: " + be.getReturnType() + "\tGot: " + children.get(1).getReturnType());
			throw new IllegalArgumentException(message);

		}
		
		private void checkType(ConditionalBooleanExpression cbe)  throws IllegalArgumentException {
			List<AtsASTNode> children = cbe.getOutgoingNodes();
			if ((cbe.getOperator() == ConditionalBooleanOperator.NOT) && (children.size() != 1)) {
				String message = cbe.getLocation().getStartLine() + ": ConditionalBooleanExpression: NOT operator should have 1 operand!\nNum of operands: " + children.size();
				throw new IllegalArgumentException(message);
			} else if ((cbe.getOperator() == ConditionalBooleanOperator.AND) && (children.size() != 2)) {
				String message = cbe.getLocation().getStartLine() + ": ConditionalBooleanExpression: AND operator should have 2 operands!\nNum of operands: " + children.size();
				throw new IllegalArgumentException(message);
			} else if ((cbe.getOperator() == ConditionalBooleanOperator.OR) && (children.size() != 2)) {
				String message = cbe.getLocation().getStartLine() + ": ConditionalBooleanExpression: OR operator should have 2 operands!\nNum of operands: " + children.size();
				throw new IllegalArgumentException(message);
			}
			// Check children for correct type
			checkType(children.get(0));
			if (children.size() == 2) checkType(children.get(1));
			boolean firstChildHasCorrectType = false;
			for (Class<?> c : getTypes(children.get(0))) {
				if (cbe.isTypeCorrect(c)) {
					firstChildHasCorrectType = true;
				}
			}
			if (!firstChildHasCorrectType) {
				String message = cbe.getLocation().getStartLine() + ": ConditionalBooleanExpression: 1st child is not a Boolean expression\n";
				message = message.concat("Expected: " + cbe.getReturnType() + "\tGot: " + children.get(0).getReturnType());
				throw new IllegalArgumentException(message);
			}
			if (children.size() == 2) {
				for (Class<?> c : getTypes(children.get(1))) {
					if (cbe.isTypeCorrect(c)) {
						return;
					}
				}
				String message = cbe.getLocation().getStartLine() + ": ConditionalBooleanExpression: 2nd child\n";
				message = message.concat("Expected: " + cbe.getReturnType() + "\tGot: " + children.get(1).getReturnType());
				throw new IllegalArgumentException(message);
			}
		}
		
		private void checkType(ForStatement fs)  throws IllegalArgumentException {
			List<AtsASTNode> children = fs.getOutgoingNodes();
			if (children.size() != 4) {
				String message = fs.getLocation().getStartLine() + ": ForStatement should have 4 children (condition, initStmt, updateStmt, stmtList)\n";
				message = message.concat("Num of children: " + children.size());
				throw new IllegalArgumentException(message);
			}
			if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
				String message = fs.getLocation().getStartLine() + ": ForStatement: Loopcondition is not a Boolean expression\n";
				message = message.concat("Expected: " + Boolean.class + "\tGot: " + children.get(0).getReturnType());
				throw new IllegalArgumentException(message);
			}
		}
		
		private void checkType(IfElseStatement is)  throws IllegalArgumentException {
			List<AtsASTNode> children = is.getOutgoingNodes();
			if (children.size() != 3) {
				String message = is.getLocation().getStartLine() + ": IfElseStatement should have 3 children (Condition, Thenstatements, Elsestatements)";
				message = message.concat("Num of children: " + children.size());
				throw new IllegalArgumentException(message);
			}
			// Check the if-condition for correct type
			checkType(children.get(0));
			// Check for correct types
			if (children.get(0).getReturnType() != Boolean.class) {
				String message = is.getLocation().getStartLine() + ": IfElseStatement: Condition is not a Boolean expression\n";
				message = message.concat("Expected: " + Boolean.class + "\tGot: " + children.get(0).getReturnType());
				throw new IllegalArgumentException(message);
			}
		}
		
		private void checkType(IfStatement is)  throws IllegalArgumentException {
			List<AtsASTNode> children = is.getOutgoingNodes();
			if (children.size() != 2) {
				String message = is.getLocation().getStartLine() + ": IfStatement should have 2 children (condition, thenStatements)\n";
				message = message.concat("Num of children: " + children.size());
				throw new IllegalArgumentException(message);
			}
			// Check the if-condition for correct type
			checkType(children.get(0));
			if (children.get(0).getReturnType() != Boolean.class) {
				String message = is.getLocation().getStartLine() + ": IfStatement: 1st child is not a Boolean expression\n";
				message = message.concat("Expected: " + Boolean.class + "\tGot: " + children.get(0).getReturnType());
				throw new IllegalArgumentException(message);
			}
		}
		
		private void checkType(RelationalExpression re)  throws IllegalArgumentException {
			List<AtsASTNode> children = re.getOutgoingNodes();
			if (children.size() != 2) {
				String message = re.getLocation().getStartLine() + ": RelationalExpression should always have 2 operands!\nNum of operands: " + children.size();
				throw new IllegalArgumentException(message);
			}
			// Check children for correct type
			checkType(children.get(0));
			checkType(children.get(1));
			
			boolean firstChildHasCorrectType = false;
			for (Class<?> c : getTypes(children.get(0))) {
				if (c.isAssignableFrom(re.getExpectingType())) {
					firstChildHasCorrectType = true;
				}
			}
			if (!firstChildHasCorrectType) {
				String message = re.getLocation().getStartLine() + ": RelationalExpression: Left operand\n";
				message = message.concat("Expected: " + re.getExpectingType() + "\tGot: " + children.get(0).getReturnType());
				throw new IllegalArgumentException(message);
			}
			
			for (Class<?> c : getTypes(children.get(1))) {
				if (c.isAssignableFrom(re.getExpectingType())) {
					return;
				}
			}
			String message = re.getLocation().getStartLine() + ": RelationalExpression: Right operand\n";
			message = message.concat("Expected: " + re.getExpectingType() + "\tGot: " + children.get(1).getReturnType());
			throw new IllegalArgumentException(message);
		}
		
		private void checkType(UnaryExpression ue)  throws IllegalArgumentException {
			List<AtsASTNode> children = ue.getOutgoingNodes();
			if (children.size() != 1) {
				String message = ue.getLocation().getStartLine() + ": UnaryExpression at line should always have 1 child!\nNum of children: " + children.size();
				throw new IllegalArgumentException(message);
			}
			// Check children for correct type
			checkType(children.get(0));
			
			if (!(children.get(0) instanceof VariableExpression)) {
				String message = ue.getLocation().getStartLine() + ": Unary operators are applicable only on variables!\nYou want to apply it on " + children.get(0).getClass().getSimpleName();
				throw new IllegalArgumentException(message);
			}
			// Check for correct types
			for (Class<?> c : getTypes(children.get(0))) {
				if (c.isAssignableFrom(ue.getReturnType())) {
					return;
				}
			}
			String message = ue.getLocation().getStartLine() + ": UnaryExpression: 1st child\n";
			message = message.concat("Expected: " + ue.getReturnType() + "\tGot: " + children.get(0).getReturnType());
			throw new IllegalArgumentException(message);
		}
		
		private void checkType(VariableDeclaration vd)  throws IllegalArgumentException {
			List<AtsASTNode> children = vd.getOutgoingNodes();
	    	if ((children.size() != 0) && (children.size() != 1)) {
	    		String message = vd.getLocation().getStartLine() + ": VariableDeclaration should have 0 or 1 child. (the value to assign)";
				throw new IllegalArgumentException(message);
	    	}
	    	if (children.size() == 0) return;
	    	
	    	for (Class<?> c : getTypes(children.get(0))) {
	    		if (vd.isTypeCorrect(c)) {
	    			return;
	    		}
	    	}
	    	String message = vd.getLocation().getStartLine() + ": VariableDeclaration Typecheck error."
	    			+ " Expression on the right side should have type " + vd.getExpectingType().getSimpleName();
	    	throw new IllegalArgumentException(message);
		}
		
		private void checkType(WhileStatement ws)  throws IllegalArgumentException {
			List<AtsASTNode> children = ws.getOutgoingNodes();
			if (children.size() != 2) {
				String message = "WhileStatement should have 2 child nodes (condition, stmtList)\n";
				message = message.concat("Number of children: " + children.size());
				throw new IllegalArgumentException(message);
			}
			if ((children.get(0) != null) && (children.get(0).getReturnType() != Boolean.class)) {
				String message = "WhileStatement: Loop condition is not a Boolean expression\n";
				message = message.concat("Expected: " + Boolean.class + "\tGot: " + children.get(0).getReturnType());
				throw new IllegalArgumentException(message);
			}
		}
		
		private Set<Class<?>> getTypes(AtsASTNode n) throws UnsupportedOperationException {
			if (n instanceof OperationInvocationExpression) {
				OperationInvocationExpression oe = (OperationInvocationExpression) n;
				String opName = oe.getOperationName().toLowerCase();
				Set<Class<?>> returnTypes = new HashSet<Class<?>>();
				if (m_existingOperations.containsKey(opName)) {
					Set<Class<?>> operationClasses = m_existingOperations.get(opName);
					for (Class<?> operationClass : operationClasses) {
							for (Method m : operationClass.getMethods()) {
								if (m.getName().equals("getResult")) {
									returnTypes.add(m.getReturnType());
								}
							}
					}
					if (returnTypes.isEmpty()) {
						throw new UnsupportedOperationException("Operation \"" + opName + "\" has no operation \"getResult()\"");
					} else {
						return returnTypes;
					}
				} else {
					throw new UnsupportedOperationException("Operation \"" + opName + "\" was not found!");
				}
			} else {
				Set<Class<?>> returnType = new HashSet<Class<?>>();
				returnType.add(n.getReturnType());
				return returnType;
			}
		}
		
	}
	
	private Map<String, Object> m_variables;
	private Map<String, Set<Class<?>>> m_existingOperations;
	private Flow m_flow;
	private AutomataDefinitionInterpreter m_automInterpreter;
	private AutomataScriptTypeChecker m_tChecker;
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private List<GenericResult<Integer>> m_testCases;
	private IAutomaton<?, ?> m_LastPrintedAutomaton;
	private int m_timeout = 60;
	private boolean m_printAutomataToFile = false;
	private PrintWriter m_printWriter;
	private String m_path = ".";
	
	
	
	public TestFileInterpreter() {
		readPreferences();
		m_variables = new HashMap<String, Object>();
		m_flow = Flow.NORMAL;
		m_automInterpreter = new AutomataDefinitionInterpreter();
		m_testCases = new ArrayList<GenericResult<Integer>>();
		m_tChecker = new AutomataScriptTypeChecker();
		m_existingOperations = getOperationClasses();
		m_LastPrintedAutomaton = null;
		UltimateServices.getInstance().setDeadline(System.currentTimeMillis() + (m_timeout * 1000));
		if (m_printAutomataToFile) {
			String path = m_path + File.separator + "automatascriptOutput" + getDateTime() + ".ats";
			File file = new File(path);
			try {
				FileWriter writer = new FileWriter(file);
				m_printWriter = new PrintWriter(writer);
			} catch (IOException e) {
				throw new AssertionError(e);
			}
		}
	}
	
	private void readPreferences() {
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.s_PLUGIN_ID);
		m_timeout = prefs.getInt(PreferenceConstants.Name_Timeout, 
				PreferenceConstants.Default_Timeout);
		m_printAutomataToFile = prefs.getBoolean(PreferenceConstants.Name_WriteToFile, 
				PreferenceConstants.Default_WriteToFile);
		m_path = prefs.get(PreferenceConstants.Name_Path, 
				PreferenceConstants.Default_Path);
	}
	
	
	private static String getDateTime() {
        DateFormat dateFormat = new SimpleDateFormat("yyyyMMddHHmmss");
        Date date = new Date();
        return dateFormat.format(date);
    }
	
	public Object interpretTestFile(AtsASTNode node) {
		List<AtsASTNode> children = node.getOutgoingNodes();
		if (children.size() != 2) {
			s_Logger.warn("AtsASTNode should have 2 children!");
			s_Logger.warn("It has: " + children.size() + " children.");
		}
		
		// Interpret automata definitions, if the file contains any.
		if (children.get(1) instanceof AutomataDefinitions) {
			m_automInterpreter.interpret((AutomataDefinitions) children.get(1));
		}
		
		m_variables.putAll(m_automInterpreter.getAutomata());
		// Type checking
		try {
			m_tChecker.checkType(children.get(0));
		} catch (IllegalArgumentException ie) {
			s_Logger.warn("Typecheck error! Testfile won't be interpreted.");
			s_Logger.info("Stack trace:");
			ie.printStackTrace();
			return null;
		}
		Object result;
		if (children.get(0) == null) {
			// File contains only automata definitions no testcases.
			result = null;
		} else if (children.get(0) instanceof StatementList) {
			result = interpret((StatementList) children.get(0));
		} else {
			throw new AssertionError("Expecting Statement List");
		}
		reportResult();
		if (m_printAutomataToFile) {
			m_printWriter.close();
		}
		return result;

	}
	
	public IAutomaton<?, ?> getLastPrintedAutomaton() {
		return m_LastPrintedAutomaton;
	}
	
	private <T> Object interpret(AssignmentExpression as) throws Exception {
		List<AtsASTNode> children = as.getOutgoingNodes();
//		if (children.size() != 2) {
//			String message = as.getLocation().getStartLine() + ": AssignmentExpression: It should have 2 operands\n";
//			message = message.concat("On the left-hand side there  must be a VariableExpression, ");
//			message = message.concat("On the right-hand side there can be an arbitrary expression.");
//			throw new RuntimeException(message);
//		}
		VariableExpression var = (VariableExpression) children.get(0);
		if (!m_variables.containsKey(var.getIdentifier())) {
			String message = as.getLocation().getStartLine() + ": AssignmentExpression: Variable " + var.getIdentifier() + " was not declared before.";
			throw new Exception(message);
		}
		Object oldValue = m_variables.get(var.getIdentifier());
		Object newValue = interpret(children.get(1));
		switch(as.getOperator()) {
		case ASSIGN: m_variables.put(var.getIdentifier(), newValue); break;
		case PLUSASSIGN: {
			Integer assignValue = ((Integer)oldValue) + ((Integer) newValue);
			m_variables.put(var.getIdentifier(), assignValue); break;
		}
		case MINUSASSIGN: {
			Integer assignValue = ((Integer)oldValue) - ((Integer) newValue);
			m_variables.put(var.getIdentifier(), assignValue); break;
		}
		case MULTASSIGN: {
			Integer assignValue = ((Integer)oldValue) * ((Integer) newValue);
			m_variables.put(var.getIdentifier(), assignValue); break;
		}
		case DIVASSIGN: {
			Integer assignValue = ((Integer)oldValue) / ((Integer) newValue);
			m_variables.put(var.getIdentifier(), assignValue); break;
		}
		default: {
			throw new UnsupportedOperationException("AssignmentExpression: This type of operator is not supported: " + as.getOperator());
		}
			
		}
		
		return oldValue;
	}
		
	private <T> Object interpret(AtsASTNode node) throws Exception {
		Object result = null;
		if (node instanceof AssignmentExpression) {
			result = interpret((AssignmentExpression) node);
		} else if (node instanceof BinaryExpression) {
			result = interpret((BinaryExpression) node);
		} else if (node instanceof BreakStatement) {
			result = interpret((BreakStatement) node);
		} else if (node instanceof ConditionalBooleanExpression) {
			result = interpret((ConditionalBooleanExpression) node);
		} else if (node instanceof ConstantExpression) {
			result = interpret((ConstantExpression) node);
		} else if (node instanceof ContinueStatement) {
			result = interpret((ContinueStatement) node);
		} else if (node instanceof ForStatement) {
			result = interpret((ForStatement) node);
		} else if (node instanceof IfElseStatement) {
			result = interpret((IfElseStatement) node);
		} else if (node instanceof IfStatement) {
			result = interpret((IfStatement) node);
		} else if (node instanceof Nestedword) {
			result = interpret((Nestedword) node);
		} else if (node instanceof NestedLassoword) {
			result = interpret((NestedLassoword) node);
		} else if (node instanceof OperationInvocationExpression) {
			result = interpret((OperationInvocationExpression) node);
		} else if (node instanceof RelationalExpression) {
			result = interpret((RelationalExpression) node);
		} else if (node instanceof ReturnStatement) {
			result = interpret((ReturnStatement) node);
		} else if (node instanceof StatementList) {
			result = interpret((StatementList) node);
		} else if (node instanceof UnaryExpression) {
			result = interpret((UnaryExpression) node);
		} else if (node instanceof VariableDeclaration) {
			result = interpret((VariableDeclaration) node);
		} else if (node instanceof VariableExpression) {
			result = interpret((VariableExpression) node);
		} else if (node instanceof WhileStatement) {
			result = interpret((WhileStatement) node);
		}
		return result;
	}

	private <T> Integer interpret(BinaryExpression be) throws Exception {
		List<AtsASTNode> children = be.getOutgoingNodes();
		Integer v1 = (Integer) interpret(children.get(0));
		Integer v2 = (Integer) interpret(children.get(1));
		
		switch(be.getOperator()) {
		case PLUS: return v1 + v2;
		case MINUS: return v1 - v2;
		case MULTIPLICATION: return v1 * v2;
		case DIVISION: return v1 / v2;
		default: throw new UnsupportedOperationException(be.getLocation().getStartLine() + ": BinaryExpression: This type of operator is not supported: " + be.getOperator());
		}
	}
	
	private <T> Object interpret(BreakStatement bst) throws Exception {
		List<AtsASTNode> children = bst.getOutgoingNodes();
		if (children.size() != 0) {
			String message = bst.getLocation().getStartLine() + ": BreakStatement: Should not have any children.\n";
			message = message.concat("Num of children: " + children.size());
			throw new Exception(message);
		}
		
		// Change the flow
		m_flow = Flow.BREAK;
		return null;
	}
	
	private <T> Boolean interpret(ConditionalBooleanExpression cbe) throws Exception{
		List<AtsASTNode> children = cbe.getOutgoingNodes();
		switch (cbe.getOperator()) {
		case NOT: return !((Boolean) interpret(children.get(0)));
		case AND: {
			Boolean v1 = (Boolean) interpret(children.get(0));
			if (!v1) {return false;} // Short-circuit and
			Boolean v2 = (Boolean) interpret(children.get(1));
			return v2;
		}
		case OR: {
			Boolean v1 = (Boolean) interpret(children.get(0));
			if (v1) {return true;} // Short-circuit or
			Boolean v2 = (Boolean) interpret(children.get(1));
			return v2;
		} 
		default: {
			String message = cbe.getLocation().getStartLine() + ": ConditionalBooleanExpression: This type of operator is not supported: " + cbe.getOperator();
	    	throw new UnsupportedOperationException(message);  
	      }
		}
	}

	private <T> Object interpret(ConstantExpression ce) {
		return ce.getValue();
	}
	
	private <T> Object interpret(ContinueStatement cst) throws Exception {
		List<AtsASTNode> children = cst.getOutgoingNodes();
		if (children.size() != 0) {
			String message = cst.getLocation().getStartLine() + ": ContinueStatement: Should not have any children.\n";
			message = message.concat("Num of children: " + children.size());
			throw new Exception(message);
		}
		// Change the flow
		m_flow  =  Flow.CONTINUE;
		return null;
	}
	
	private <T> Object interpret(ForStatement fs) throws Exception {
		List<AtsASTNode> children = fs.getOutgoingNodes();
		
		Boolean loopCondition = false;
		// If the loopcondition is missing, we just execute the loop forever
		if (children.get(0) == null) {
			loopCondition = true;
		}
		// execute the initialization statement, if one is existing
		if (children.get(1) != null) {
			interpret(children.get(1));
		}
		if (loopCondition) {
			for (;;) {
				List<AtsASTNode> statementList =  children.get(3).getOutgoingNodes();
			secondLoop:
				for (int i = 0; i < statementList.size(); i++) {
					interpret(statementList.get(i));
					if (m_flow != Flow.NORMAL) {
						switch (m_flow) {
						case BREAK:
						case RETURN: {
							m_flow = Flow.NORMAL;
							return null;
						}
						case CONTINUE: {
							m_flow = Flow.NORMAL;
							break secondLoop;
						}
						}
					}
				}
				// execute the updatestatement
				if (children.get(2) != null) {
					interpret(children.get(2));
				}
			}
		} else {
			for (;(Boolean)interpret(children.get(0));) {
				List<AtsASTNode> statementList =  children.get(3).getOutgoingNodes();
			secondLoop:
				for (int i = 0; i < statementList.size(); i++) {
					interpret(statementList.get(i));
					if (m_flow != Flow.NORMAL) {
						switch (m_flow) {
						case BREAK:
						case RETURN: {
							m_flow = Flow.NORMAL;
							return null;
						}
						case CONTINUE: {
							m_flow = Flow.NORMAL;
							break secondLoop;
						}
						}
					}
				}
				// execute the updatestatement
				if (children.get(2) != null) {
					interpret(children.get(2));
				}
			}
		}
		return null;
	}
	private <T> Object interpret(IfElseStatement is) throws Exception {
		List<AtsASTNode> children = is.getOutgoingNodes();
		
		// children(0) is the condition
		if ((Boolean) interpret(children.get(0))) {
			interpret(children.get(1));
		} else {
			interpret(children.get(2));
		}
		return null;
	}
	
	private <T> Object interpret(IfStatement is) throws Exception {
		List<AtsASTNode> children = is.getOutgoingNodes();
		if ((Boolean) interpret(children.get(0))) {
			for (int i = 1; i < children.size(); i++) {
				interpret(children.get(i));
			}
		}
		return null;
	}
	
	private <T> NestedWord<String> interpret(Nestedword nw) throws Exception {
		return new NestedWord<String>(nw.getWordSymbols(), nw.getNestingRelation());
	}
	
	private <T> NestedLassoWord<String> interpret(NestedLassoword nw) throws Exception {
		NestedWord<String> stem = interpret(nw.getStem());
		NestedWord<String> loop = interpret(nw.getLoop());
		return new NestedLassoWord<String>(stem, loop);
	}
	
	private <T> Object interpret(OperationInvocationExpression oe) throws Exception {
		List<AtsASTNode> children = oe.getOutgoingNodes();
		if (children.size() != 1) {
			String message = oe.getLocation().getStartLine() + ": OperationExpression should have only 1 child (ArgumentList)";
			message = message.concat("Num of children: " + children.size());
			throw new IllegalArgumentException(message);
		}
		
		ArrayList<Object> arguments = null;
		List<AtsASTNode> argsToInterpret = null;
		if (children.get(0) != null) {
			argsToInterpret = children.get(0).getOutgoingNodes();
			arguments = new ArrayList<Object>(argsToInterpret.size());
			// Interpret the arguments of this operation
			for (int i = 0; i < argsToInterpret.size(); i++) {
				arguments.add(interpret(argsToInterpret.get(i)));
			}
		}

		Object result = null;

		if (oe.getOperationName().equalsIgnoreCase("assert") && arguments.size() == 1) {
			result = arguments.get(0);
			if (result instanceof Boolean) {
				if ((Boolean) result) {
					m_testCases.add(new GenericResult<Integer>(oe.getLocation().getStartLine(), 
									Activator.s_PLUGIN_ID, 
							        null,
							        oe.getLocation(), 
							        "Assertion holds.", 
							        oe.getAsString(), 
							        Severity.INFO));
				} else {
					m_testCases.add(new GenericResult<Integer>(oe.getLocation().getStartLine(), 
									Activator.s_PLUGIN_ID, 
									null,
									oe.getLocation(), 
									"Assertion violated!", 
									oe.getAsString(), 
									Severity.ERROR));
				}
			}
		} else if (oe.getOperationName().equalsIgnoreCase("print")) {
			String argsAsString = children.get(0).getAsString();
			ILocation loc = children.get(0).getLocation();
			printMessage(Severity.INFO, "Printing " + argsAsString, "print:", loc);
			for (Object o : arguments) {
				if (o instanceof IAutomaton) {
					m_LastPrintedAutomaton = (IAutomaton<?, ?>) o;
					String automatonAsString = (new AtsDefinitionPrinter(o)).getDefinitionAsString();
					printMessage(Severity.INFO, automatonAsString, oe.getAsString(), loc);
					if (m_printAutomataToFile) {
						String comment = "/* " + oe.getAsString() + " */";
						m_printWriter.println(comment);
						m_printWriter.println(automatonAsString);
					}
					
				} else {
					s_Logger.info(o.toString());
					printMessage(Severity.INFO, o.toString(), oe.getAsString(), loc);
					if (m_printAutomataToFile) {
						String comment = "/* " + oe.getAsString() + " */";
						m_printWriter.println(comment);
						m_printWriter.println(o.toString());
					}
				}
				
			}
			
		} else {
			IOperation op = getAutomataOperation(oe, arguments);
			if (op != null) {
				result = op.getResult();
			} 
		}
		return result;
	}
	
	private <T> Boolean interpret(RelationalExpression re) throws Exception{
		List<AtsASTNode> children = re.getOutgoingNodes();
		if (re.getExpectingType() == Integer.class) {
			Integer v1 = (Integer) interpret(children.get(0));
			Integer v2 = (Integer) interpret(children.get(1));
			switch (re.getOperator()) {
			case GREATERTHAN: return v1 > v2;
			case LESSTHAN: return v1 < v2;
			case GREATER_EQ_THAN: return v1 >= v2;
			case LESS_EQ_THAN: return v1 <= v2;
			case EQ: return v1 == v2;
			case NOT_EQ: return v1 != v2;
			default: throw new UnsupportedOperationException(re.getLocation().getStartLine() + ": RelationalExpression: This type of operator is not supported: " + re.getOperator());
			}
		}
		return null;
	}
	
	private <T> Object interpret(ReturnStatement rst) throws Exception {
		List<AtsASTNode> children = rst.getOutgoingNodes();
		if ((children.size() != 0) && (children.size() != 1)) {
			String message = rst.getLocation().getStartLine() + ": ReturnStatement: Too many children\n";
			message = message.concat("Num of children: " + children.size());
			throw new Exception(message);
		}
		// Change the flow
		m_flow = Flow.RETURN;
		if (children.size() == 0) {
			return null;
		} else {
			return interpret(children.get(0));
		}
	}
	
	private <T> Object interpret(StatementList stmtList) {
		for (AtsASTNode stmt : stmtList.getOutgoingNodes()) {
			try {
				interpret(stmt);
			} catch (Exception e) {
				if (e.getMessage().equals(UNKNOWN_OPERATION)) {
					// do nothing - result was already reported
				} else {
					TestFileInterpreter.printMessage(Severity.ERROR, e.toString() 
							+ System.getProperty("line.separator") + e.getStackTrace(), 
							"Exception thrown.", stmt.getLocation());
				}
			}
		}
		return null;
	}
	
    private <T> Integer interpret(UnaryExpression ue) throws Exception {
		  List<AtsASTNode> children = ue.getOutgoingNodes();
		  
		  VariableExpression var = (VariableExpression) children.get(0);
		  Integer oldVal = (Integer)interpret(var);
	      
	      switch(ue.getOperator()) {
	      case EXPR_PLUSPLUS: {
	    	  m_variables.put(var.getIdentifier(), oldVal + 1);
	    	  return oldVal;
	      }
	      case EXPR_MINUSMINUS: {
	    	  m_variables.put(var.getIdentifier(), oldVal - 1);
	    	  return oldVal;
	      }
	      case PLUSPLUS_EXPR: {
	    	  m_variables.put(var.getIdentifier(), oldVal + 1);
	    	  return oldVal + 1;
	      }
	      case MINUSMINUS_EXPR: {
	    	  m_variables.put(var.getIdentifier(), oldVal - 1);
	    	  return oldVal - 1;
	      }
	      default: {
	    	String message =  ue.getLocation().getStartLine() + ": UnaryExpression: This type of operator is not supported: " + ue.getOperator(); 
	    	throw new UnsupportedOperationException(message);  
	      }
	      }
		}
	
    private <T> Object interpret(VariableDeclaration vd) throws Exception {
    	List<AtsASTNode> children = vd.getOutgoingNodes();
    	Object value = null;
    	if (children.size() == 1) {
    		value = interpret(children.get(0));
    	}
    	
    	for (String id : vd.getIdentifiers()) {
    		m_variables.put(id, value);
    	}
    	return null;
    }
    
	private <T> Object interpret(VariableExpression ve) throws Exception {
		if (!m_variables.containsKey(ve.getIdentifier())) {
			String message = "VariableExpression: Variable " + ve.getIdentifier() + " at line " + ve.getLocation().getStartLine() + " was not declared.";
			throw new RuntimeException(message);
		}
		
		return m_variables.get(ve.getIdentifier());
	}
	
	private <T> Object interpret(WhileStatement ws) throws Exception {
		List<AtsASTNode> children = ws.getOutgoingNodes();
		Boolean loopCondition = (Boolean) interpret(children.get(0));
		while (loopCondition) {
			List<AtsASTNode> statementList = children.get(1).getOutgoingNodes();
			secondLoop:
				for (int i = 0; i < statementList.size(); i++) {
					interpret(statementList.get(i));
					if (m_flow != Flow.NORMAL) {
						switch (m_flow) {
						case BREAK:
						case RETURN: {
							m_flow = Flow.NORMAL;
							return null;
						}
						case CONTINUE: {
							m_flow = Flow.NORMAL;
							break secondLoop;
						}
						}
					}
				}
			loopCondition = (Boolean) interpret(children.get(0));
		}
		
		return null;
	}

	private void reportResult() {
		String testCasesSummary = "All testcases passed.";
		s_Logger.info("----------------- Test Summary -----------------");
		for (GenericResult<Integer> test : m_testCases) {
			UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, test);
			if (test.getSeverity() == Severity.ERROR) testCasesSummary = "Some testcases failed.";
			reportToLogger(Severity.INFO, "Line " + test.getLocation().getStartLine() + ": " + test.getShortDescription());
		}
		// Report summary of the testcases/
		if (m_testCases.isEmpty()) {
			printMessage(Severity.WARNING, "No testcases defined!", "Warning" ,  null);
		} else {
			reportToLogger(Severity.INFO, testCasesSummary);
		}	
	}
	
	
	/**
	 * Reports the given string to the logger
	 * and to Ultimate as a NoResult.
	 * @param sev the Severity
	 * @param longDescr the string to be reported
	 * @param loc the location of the String
	 */
	static void printMessage(Severity sev, String longDescr, String shortDescr, ILocation loc) {
		reportToUltimate(sev, longDescr, shortDescr, loc);
		reportToLogger(sev, longDescr);
	}
	
	/**
	 * Reports the given string with the given severity to Ultimate as a NoResult
	 * @param sev the severity
	 * @param longDescr the string to be reported
	 * @param loc the location of the string
	 */
	private static void reportToUltimate(Severity sev, String longDescr, String shortDescr, ILocation loc) {
			GenericResult<Integer> res = new GenericResult<Integer> ((loc != null ? loc.getStartLine() : 0),
					                     Activator.s_PLUGIN_ID, null,
					                     loc,
					                     shortDescr, longDescr, 
					                     sev);
			UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, res);
	}
	
	/**
	 * Reports the given string with the given severity to the logger 
	 * @param sev the severity of the string
	 * @param toPrint the string to be printed
	 */
	private static void reportToLogger(Severity sev, String toPrint) {
		switch (sev){
		case ERROR: s_Logger.error(toPrint); break;
		case INFO: s_Logger.info(toPrint); break;
		case WARNING: s_Logger.warn(toPrint); break;
		default: s_Logger.info(toPrint); 
		}
	}

	private IOperation getAutomataOperation(OperationInvocationExpression oe, ArrayList<Object> arguments) throws Exception {
		String operationName = oe.getOperationName().toLowerCase();
		IOperation result = null;
		if (m_existingOperations.containsKey(operationName)) {
			Set<Class<?>> operationClasses = m_existingOperations.get(operationName);
			for (Class<?> operationClass : operationClasses) {
				Constructor<?>[] operationConstructors = operationClass.getConstructors();
				// Find the constructor which expects the correct arguments
				for (Constructor<?> c : operationConstructors) {
					if (allArgumentsHaveCorrectTypeForThisConstructor(c, arguments)) {
						try {
							result = (IOperation) c.newInstance(arguments.toArray());
							return result;
						} catch (InstantiationException e) {
							e.printStackTrace();
							throw new AssertionError(e);
						} catch (IllegalAccessException e) {
							e.printStackTrace();
							throw new AssertionError(e);
						} catch (IllegalArgumentException e) {
							e.printStackTrace();
							throw new AssertionError(e);
						} catch (InvocationTargetException e) {
							throw (Exception) e.getCause();
						}
					}
				}					
			}
		} else {
			String shortDescr = "Unsupported operation \"" + operationName + "\"";
			String allOperations = (new ListExistingOperations(m_existingOperations)).prettyPrint();
			String longDescr = "We support only the following operations " + System.getProperty("line.separator") + allOperations;
			reportToUltimate(Severity.ERROR, longDescr, shortDescr, oe.getLocation());
			s_Logger.warn(shortDescr);
			throw new UnsupportedOperationException(UNKNOWN_OPERATION);
		}
		return result;
	}
	
	
	private boolean allArgumentsHaveCorrectTypeForThisConstructor(Constructor<?> c, List<Object> arguments) {
		int i = 0;
		int minArgSize = (c.getParameterTypes().length > arguments.size() ? arguments.size() : c.getParameterTypes().length);
		for (Class<?> type : c.getParameterTypes()) {
			if ((i >= minArgSize) || !(type.isAssignableFrom(arguments.get(i).getClass()))) {
				return false;
			}
			++i;
		}
		return true;
	}
	

	/**
	 * 
	 * @return Returns a map from String to class objects from the classes found in the directories.
 	 */
	private static Map<String, Set<Class<?>>> getOperationClasses() {
		Map<String, Set<Class<?>>> result = new HashMap<String, Set<Class<?>>>();
		String[] baseDirs = {"/de/uni_freiburg/informatik/ultimate/automata/nwalibrary/operations",
				              "/de/uni_freiburg/informatik/ultimate/automata/nwalibrary/buchiNwa",
				              "/de/uni_freiburg/informatik/ultimate/automata/petrinet/julian"};
		for (String baseDir : baseDirs) {
			ArrayDeque<String> dirs = new ArrayDeque<String>();
			dirs.add("");
			while (!dirs.isEmpty()) {
				String dir = dirs.removeFirst();
				String[] files = filesInDirectory(baseDir + "/" + dir);
				for (String file : files) {
					if (file.endsWith(".class")) {
						String fileWithoutSuffix = file.substring(0, file.length()-6);
						String baseDirInPackageFormat = baseDir.replaceAll("/", ".");
						if (baseDirInPackageFormat.charAt(0) == '.') {
							baseDirInPackageFormat = baseDirInPackageFormat.substring(1);
						}
						String path = "";
						if (dir.isEmpty()) {
							path = baseDirInPackageFormat + "." + fileWithoutSuffix;
						} else {
							path = baseDirInPackageFormat + "." + dir + "." + fileWithoutSuffix;
						}
						Class<?> clazz = null;
						try {
							clazz = Class.forName(path);
						} catch (ClassNotFoundException e) {
							e.printStackTrace();
							s_Logger.error("Couldn't load/find class " + path);
							break;
						}
						if ((clazz != null) && (classImplementsIOperationInterface(clazz))) {
							String operationName = fileWithoutSuffix.toLowerCase();
							if (result.containsKey(operationName)) {
								Set<Class<?>> s = result.get(operationName);
								s.add(clazz);
							} else {
								Set<Class<?>> s = new HashSet<Class<?>>();
								s.add(clazz);
								result.put(operationName, s);
							}
							
							
						}
					}
					// if the file has no ending, it may be a directory
					else if (!file.contains(".")) {
						try {
							if (isDirectory(baseDir + "/" + file)) {
								dirs.addLast(file);
							}
						} catch (Exception e) {
							
						}
					}
				}
			}
		}
		return result;
	}
	
	private static boolean classImplementsIOperationInterface(Class<?> c) {
		Class<?>[] implementedInterfaces = c.getInterfaces();
		for (Class<?> interFace : implementedInterfaces) {
			if (interFace.equals(IOperation.class)) {
				return true;
			}
		}
		return false;
	}
	
	private static boolean isDirectory(String dir) {
		URL dirURL = IOperation.class.getClassLoader().getResource(dir);
		if (dirURL == null) return false;
		else return dirURL.getProtocol().equals("bundleresource");
	}
	
	/**
	 * Return the filenames of the files in the given
	 * directory.
	 * We use the classloader to get the URL of this folder. We support only
	 * URLs with protocol <i>file</i> and <i>bundleresource</i>.
	 * At the moment these are the only ones that occur in Website and
	 * WebsiteEclipseBridge.
	 */
	private static String[] filesInDirectory(String dir) {
		URL dirURL = IOperation.class.getClassLoader().getResource(dir);
		if (dirURL == null) {
			// throw new UnsupportedOperationException("Directory \"" + dir + "\" does not exist");
			s_Logger.error("Directory \"" + dir + "\" does not exist");
			return new String[0];
		}
		String protocol = dirURL.getProtocol();
		File dirFile = null;
		if (protocol.equals("file")) {
			try {
				dirFile = new File(dirURL.toURI());
			} catch (URISyntaxException e) {
				e.printStackTrace();
				// throw new UnsupportedOperationException("Directory \"" + dir + "\" does not exist");
				s_Logger.error("Directory \"" + dir + "\" does not exist");
				return new String[0];
			}
		} else if (protocol.equals("bundleresource")) {
			try {
				URL fileURL = FileLocator.toFileURL(dirURL);
				dirFile = new File(fileURL.toURI());
			} catch (Exception e) {
				e.printStackTrace();
				// throw new UnsupportedOperationException("Directory \"" + dir + "\" does not exist");
				s_Logger.error("Directory \"" + dir + "\" does not exist");
				return new String[0];
			}
		} else {
			throw new UnsupportedOperationException("unknown protocol");
		}
		String[] files = dirFile.list();
		return files;
	}
	
}
