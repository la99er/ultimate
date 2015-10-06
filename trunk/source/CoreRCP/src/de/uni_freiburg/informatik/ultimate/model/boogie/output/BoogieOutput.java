/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Boogie printer observer.
 */
package de.uni_freiburg.informatik.ultimate.model.boogie.output;

import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ParentEdge;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;

/**
 * @author hoenicke
 */
public class BoogieOutput {

	private static final String sLinebreak = System.getProperty("line.separator");

	/**
	 * The file writer.
	 */
	PrintWriter m_Writer;

	public BoogieOutput(PrintWriter output) {
		m_Writer = output;
	}

	public void printBoogieProgram(Unit unit) {
		for (Declaration d : unit.getDeclarations()) {
			if (d instanceof TypeDeclaration)
				printTypeDeclaration((TypeDeclaration) d);
			else if (d instanceof ConstDeclaration)
				printConstDeclaration((ConstDeclaration) d);
			else if (d instanceof VariableDeclaration)
				printVarDeclaration((VariableDeclaration) d, "");
			else if (d instanceof FunctionDeclaration)
				printFunctionDeclaration((FunctionDeclaration) d);
			else if (d instanceof Axiom)
				printAxiom((Axiom) d);
			else if (d instanceof Procedure)
				printProcedure((Procedure) d);
		}
	}

	/**
	 * Append a given expression.
	 * 
	 * @param sb
	 *            the StringBUilder to append to.
	 * @param expr
	 *            the expression to print.
	 * @param precedence
	 *            the precedence of the surrounding operator. 0: if and only if
	 *            1: implies 3: logical or 4: logical and 5: comparison 6:
	 *            bitvec concat 7: addition 8: multiplication 9: unary
	 *            minus/logical not 10: struct/array/bitvector access 11: old
	 */
	private void appendExpression(StringBuilder sb, Expression expr, int precedence) {
		if (expr instanceof BinaryExpression) {
			BinaryExpression binexpr = (BinaryExpression) expr;
			int opPrec, lPrec, rPrec;
			String op;
			switch (binexpr.getOperator()) {
			case LOGICIFF:
				op = " <==> ";
				opPrec = 0;
				lPrec = 1;
				rPrec = 0;
				break;
			case LOGICIMPLIES:
				op = " ==> ";
				opPrec = 1;
				lPrec = 2;
				rPrec = 1;
				break;
			case LOGICOR:
				op = " || ";
				opPrec = 3;
				lPrec = 5;
				rPrec = 3;
				break;
			case LOGICAND:
				if (precedence == 3)
					precedence = 5;
				op = " && ";
				opPrec = 4;
				lPrec = 5;
				rPrec = 4;
				break;
			case COMPEQ:
				op = " == ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case COMPNEQ:
				op = " != ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case COMPLT:
				op = " < ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case COMPLEQ:
				op = " <= ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case COMPGT:
				op = " > ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case COMPGEQ:
				op = " >= ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case COMPPO:
				op = " <: ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case BITVECCONCAT:
				op = " ++ ";
				opPrec = 6;
				lPrec = 6;
				rPrec = 7;
				break;
			case ARITHPLUS:
				op = " + ";
				opPrec = 7;
				lPrec = 7;
				rPrec = 8;
				break;
			case ARITHMINUS:
				op = " - ";
				opPrec = 7;
				lPrec = 7;
				rPrec = 8;
				break;
			case ARITHMUL:
				op = " * ";
				opPrec = 8;
				lPrec = 8;
				rPrec = 9;
				break;
			case ARITHDIV:
				op = " / ";
				opPrec = 8;
				lPrec = 8;
				rPrec = 9;
				break;
			case ARITHMOD:
				op = " % ";
				opPrec = 8;
				lPrec = 8;
				rPrec = 9;
				break;
			default:
				throw new IllegalArgumentException(expr.toString());
			}
			if (precedence > opPrec)
				sb.append("(");
			appendExpression(sb, binexpr.getLeft(), lPrec);
			sb.append(op);
			appendExpression(sb, binexpr.getRight(), rPrec);
			if (precedence > opPrec)
				sb.append(")");
		} else if (expr instanceof UnaryExpression) {
			UnaryExpression unexpr = (UnaryExpression) expr;
			String op;
			int opPrec;
			switch (unexpr.getOperator()) {
			case ARITHNEGATIVE:
				op = "-";
				opPrec = 9;
				break;
			case LOGICNEG:
				op = "!";
				opPrec = 9;
				break;
			case OLD:
				op = "old";
				opPrec = 11;
				break;
			default:
				throw new IllegalArgumentException(expr.toString());
			}
			if (precedence > opPrec)
				sb.append("(");
			sb.append(op);
			if (op == "old") {
				sb.append("(");
				appendExpression(sb, unexpr.getExpr(), 0);
				sb.append(")");
			} else
				appendExpression(sb, unexpr.getExpr(), opPrec);
			if (precedence > opPrec)
				sb.append(")");
		} else if (expr instanceof BitVectorAccessExpression) {
			BitVectorAccessExpression bvexpr = (BitVectorAccessExpression) expr;
			if (precedence > 10)
				sb.append("(");
			appendExpression(sb, bvexpr.getBitvec(), 10);
			sb.append("[").append(bvexpr.getEnd()).append(":");
			sb.append(bvexpr.getStart()).append("]");
			if (precedence > 10)
				sb.append(")");
		} else if (expr instanceof StructAccessExpression) {
			StructAccessExpression strexpr = (StructAccessExpression) expr;
			if (precedence > 10)
				sb.append("(");
			appendExpression(sb, strexpr.getStruct(), 10);
			sb.append("!");
			sb.append(strexpr.getField());
			if (precedence > 10)
				sb.append(")");
		} else if (expr instanceof ArrayAccessExpression) {
			ArrayAccessExpression arrexpr = (ArrayAccessExpression) expr;
			if (precedence > 10)
				sb.append("(");
			appendExpression(sb, arrexpr.getArray(), 10);
			sb.append("[");
			String comma = "";
			for (Expression indExpr : arrexpr.getIndices()) {
				sb.append(comma);
				appendExpression(sb, indExpr, 0);
				comma = ",";
			}
			sb.append("]");
			if (precedence > 10)
				sb.append(")");
		} else if (expr instanceof ArrayStoreExpression) {
			ArrayStoreExpression arrexpr = (ArrayStoreExpression) expr;
			if (precedence > 10)
				sb.append("(");
			appendExpression(sb, arrexpr.getArray(), 10);
			sb.append("[");
			String comma = "";
			for (Expression indExpr : arrexpr.getIndices()) {
				sb.append(comma);
				appendExpression(sb, indExpr, 0);
				comma = ",";
			}
			sb.append(" := ");
			appendExpression(sb, arrexpr.getValue(), 0);
			sb.append("]");
			if (precedence > 10)
				sb.append(")");
		} else if (expr instanceof BitvecLiteral) {
			BitvecLiteral bvlit = (BitvecLiteral) expr;
			sb.append(bvlit.getValue()).append("bv").append(bvlit.getLength());
		} else if (expr instanceof IntegerLiteral) {
			sb.append(((IntegerLiteral) expr).getValue());
		} else if (expr instanceof RealLiteral) {
			sb.append(((RealLiteral) expr).getValue());
		} else if (expr instanceof BooleanLiteral) {
			sb.append(((BooleanLiteral) expr).getValue());
		} else if (expr instanceof StringLiteral) {
			sb.append('"').append(((StringLiteral) expr).getValue()).append('"');
		} else if (expr instanceof StructConstructor) {
			StructConstructor struct = (StructConstructor) expr;
			String comma = "";
			sb.append("{ ");
			String[] fieldNames = struct.getFieldIdentifiers();
			Expression[] fieldExprs = struct.getFieldValues();
			for (int i = 0; i < fieldNames.length; i++) {
				sb.append(comma).append(fieldNames[i]);
				sb.append(": ");
				appendExpression(sb, fieldExprs[i]);
				comma = ", ";
			}
			sb.append(" }");
		} else if (expr instanceof WildcardExpression) {
			sb.append("*");
		} else if (expr instanceof IdentifierExpression) {
			sb.append(((IdentifierExpression) expr).getIdentifier());
		} else if (expr instanceof FunctionApplication) {
			FunctionApplication app = (FunctionApplication) expr;
			sb.append(app.getIdentifier()).append("(");
			String comma = "";
			for (Expression arg : app.getArguments()) {
				sb.append(comma);
				appendExpression(sb, arg, 0);
				comma = ", ";
			}
			sb.append(")");
		} else if (expr instanceof IfThenElseExpression) {
			IfThenElseExpression ite = (IfThenElseExpression) expr;
			/* we always append parentheses, just to be sure. */
			sb.append("(if ");
			appendExpression(sb, ite.getCondition(), 0);
			sb.append(" then ");
			appendExpression(sb, ite.getThenPart(), 0);
			sb.append(" else ");
			appendExpression(sb, ite.getElsePart(), 0);
			sb.append(")");
		} else if (expr instanceof QuantifierExpression) {
			QuantifierExpression quant = (QuantifierExpression) expr;
			sb.append("(");
			sb.append(quant.isUniversal() ? "forall" : "exists");
			String[] typeParams = quant.getTypeParams();
			if (typeParams.length > 0) {
				sb.append(" <");
				String comma = "";
				for (String t : typeParams) {
					sb.append(comma).append(t);
					comma = ",";
				}
				sb.append(">");
			}
			if (quant.getParameters().length > 0) {
				sb.append(" ");
				appendVarList(sb, quant.getParameters());
			}
			sb.append(" :: ");
			appendAttributes(sb, quant.getAttributes());
			appendExpression(sb, quant.getSubformula(), 0);
			sb.append(")");
		} else {
			throw new IllegalArgumentException(expr.toString());
		}
	}

	/**
	 * Appends a type.
	 * 
	 * @param sb
	 *            the StringBuilder to append to.
	 * @param type
	 *            ASTType
	 * @param precedence
	 *            TODO: what is precedence?
	 */
	private void appendType(StringBuilder sb, ASTType type, int precedence) {
		if (type instanceof NamedType) {
			NamedType nt = (NamedType) type;
			ASTType[] args = nt.getTypeArgs();

			if (precedence > 0 && args.length > 0)
				sb.append("(");
			sb.append(nt.getName());
			for (int i = 0; i < args.length; i++) {
				sb.append(" ");
				appendType(sb, args[i], i < args.length - 1 ? 2 : 1);
			}
			if (precedence > 0 && args.length > 0)
				sb.append(")");
		} else if (type instanceof ArrayType) {
			ArrayType at = (ArrayType) type;
			if (precedence > 1)
				sb.append("(");
			if (at.getTypeParams().length > 0) {
				String comma = "<";
				for (String id : at.getTypeParams()) {
					sb.append(comma).append(id);
					comma = ",";
				}
				sb.append(">");
			}
			String comma = "[";
			for (ASTType indexType : at.getIndexTypes()) {
				sb.append(comma);
				appendType(sb, indexType, 0);
				comma = ",";
			}
			sb.append("]");
			appendType(sb, at.getValueType(), 0);
			if (precedence > 1)
				sb.append(")");
		} else if (type instanceof StructType) {
			StructType st = (StructType) type;
			if (precedence > 1)
				sb.append("(");
			sb.append("{ ");
			appendVarList(sb, st.getFields());
			sb.append(" }");
			if (precedence > 1)
				sb.append(")");
		} else if (type instanceof PrimitiveType) {
			sb.append(((PrimitiveType) type).getName());
		}
	}

	/**
	 * Append attributes.
	 * 
	 * @param sb
	 *            the StringBuilder to append to.
	 * @param attributes
	 *            the attributes to handle.
	 */
	private void appendAttributes(StringBuilder sb, Attribute[] attributes) {
		for (Attribute a : attributes) {
			if (a instanceof NamedAttribute) {
				NamedAttribute attr = (NamedAttribute) a;
				sb.append("{ :").append(attr.getName());
				String comma = " ";
				for (Expression value : attr.getValues()) {
					sb.append(comma);
					appendExpression(sb, value, 0);
					comma = ",";
				}
				sb.append(" } ");
			} else if (a instanceof Trigger) {
				sb.append("{ ");
				String comma = "";
				for (Expression value : ((Trigger) a).getTriggers()) {
					sb.append(comma);
					appendExpression(sb, value, 0);
					comma = ",";
				}
				sb.append(" } ");
			}
		}
	}

	public void appendExpression(StringBuilder sb, Expression expr) {
		appendExpression(sb, expr, 0);
	}

	/**
	 * Append the string representation of vls (comma separated list of
	 * declarations) to the stringbuilder sb.
	 * 
	 * @param sb
	 *            the string builder where we append to
	 * @param vls
	 *            the variable declaration that are appended.
	 */
	public void appendVarList(StringBuilder sb, VarList[] vls) {
		String comma = "";
		for (VarList vl : vls) {
			sb.append(comma);
			if (vl.getIdentifiers().length > 0) {
				/*
				 * identifiers array can only be empty for function parameters
				 * (unnamed parameter).
				 */
				String subcomma = "";
				for (String id : vl.getIdentifiers()) {
					sb.append(subcomma).append(id);
					subcomma = ", ";
				}
				sb.append(" : ");
			}
			appendType(sb, vl.getType(), 0);
			if (vl.getWhereClause() != null) {
				sb.append(" where ");
				appendExpression(sb, vl.getWhereClause(), 0);
			}
			comma = ", ";
		}
	}

	/**
	 * Print type declaration.
	 * 
	 * @param decl
	 *            the type declaration.
	 */
	public void printTypeDeclaration(TypeDeclaration decl) {
		StringBuilder sb = new StringBuilder();
		sb.append("type ");
		appendAttributes(sb, decl.getAttributes());
		if (decl.isFinite())
			sb.append("finite ");
		sb.append(decl.getIdentifier());
		for (String args : decl.getTypeParams())
			sb.append(" ").append(args);
		ASTType synonym = decl.getSynonym();
		if (synonym != null) {
			sb.append(" = ");
			appendType(sb, synonym, 0);
		}
		sb.append(";");
		m_Writer.println(sb.toString());
	}

	/**
	 * Print function declaration.
	 * 
	 * @param decl
	 *            the function declaration.
	 */
	public void printFunctionDeclaration(FunctionDeclaration decl) {
		StringBuilder sb = new StringBuilder();
		sb.append("function ");
		appendAttributes(sb, decl.getAttributes());
		sb.append(decl.getIdentifier());
		if (decl.getTypeParams().length > 0) {
			String comma = "<";
			for (String id : decl.getTypeParams()) {
				sb.append(comma).append(id);
				comma = ",";
			}
			sb.append(">");
		}
		sb.append("(");
		appendVarList(sb, decl.getInParams());
		sb.append(") returns (");
		appendVarList(sb, new VarList[] { decl.getOutParam() });
		sb.append(")");
		if (decl.getBody() != null) {
			sb.append(" { ");
			appendExpression(sb, decl.getBody(), 0);
			sb.append(" }");
		} else
			sb.append(";");
		m_Writer.println(sb.toString());
	}

	/**
	 * Print procedure.
	 * 
	 * @param decl
	 *            the procedure to print.
	 */
	public void printProcedure(Procedure decl) {
		StringBuilder sb = new StringBuilder();
		appendProcedure(sb, decl);
		m_Writer.print(sb.toString());
	}

	public void appendProcedure(StringBuilder sb, Procedure decl) {
		if (decl.getSpecification() != null) {
			sb.append("procedure ");
		} else {
			sb.append("implementation ");
		}
		appendAttributes(sb, decl.getAttributes());
		sb.append(decl.getIdentifier());
		if (decl.getTypeParams().length > 0) {
			String comma = "<";
			for (String id : decl.getTypeParams()) {
				sb.append(comma).append(id);
				comma = ",";
			}
			sb.append(">");
		}
		sb.append("(");
		appendVarList(sb, decl.getInParams());
		sb.append(") returns (");
		appendVarList(sb, decl.getOutParams());
		sb.append(")");
		if (decl.getBody() == null)
			sb.append(";");
		if (decl.getSpecification() != null) {
			sb.append(sLinebreak);
			for (Specification spec : decl.getSpecification()) {
				appendSpecification(sb, spec);
			}
		}
		if (decl.getBody() != null) {
			sb.append("{" + sLinebreak);
			appendBody(sb, decl.getBody());
			sb.append("}" + sLinebreak);
		}
		sb.append(sLinebreak);
	}

	/**
	 * Print specification.
	 * 
	 * @param spec
	 *            the specification to print.
	 */
	public void printSpecification(Specification spec) {
		StringBuilder sb = new StringBuilder();
		appendSpecification(sb, spec);
		m_Writer.print(sb.toString());
	}

	public void appendSpecification(StringBuilder sb, Specification spec) {
		if (spec.isFree())
			sb.append("free ");
		if (spec instanceof RequiresSpecification) {
			sb.append("requires ");
			appendExpression(sb, ((RequiresSpecification) spec).getFormula(), 0);
		} else if (spec instanceof EnsuresSpecification) {
			sb.append("ensures ");
			appendExpression(sb, ((EnsuresSpecification) spec).getFormula(), 0);
		} else if (spec instanceof ModifiesSpecification) {
			sb.append("modifies ");
			String comma = "";
			for (VariableLHS id : ((ModifiesSpecification) spec).getIdentifiers()) {
				sb.append(comma).append(id.getIdentifier());
				comma = ", ";
			}
		} else if (spec instanceof LoopInvariantSpecification) {
			sb.append("invariant ");
			appendExpression(sb, ((LoopInvariantSpecification) spec).getFormula(), 0);
		} else {
			throw new IllegalArgumentException(spec.toString());
		}
		sb.append(";").append(sLinebreak);
	}

	/**
	 * Print body.
	 * 
	 * @param body
	 *            the body to print.
	 */
	public void printBody(Body body) {
		StringBuilder sb = new StringBuilder();
		appendBody(sb, body);
		m_Writer.print(sb.toString());
	}

	public void appendBody(StringBuilder sb, Body body) {
		for (VariableDeclaration decl : body.getLocalVars()) {
			appendVariableDeclaration(sb, decl, "    ");
		}
		if (body.getLocalVars().length > 0) {
			sb.append(sLinebreak);
		}
		appendBlock(sb, body.getBlock(), "");
	}

	/**
	 * Print block.
	 * 
	 * @param block
	 *            the block to print.
	 * @param indent
	 *            the current indent level.
	 */
	public void printBlock(Statement[] block, String indent) {
		StringBuilder sb = new StringBuilder();
		appendBlock(sb, block, indent);
		m_Writer.print(sb.toString());
	}

	public void appendBlock(StringBuilder sb, Statement[] block) {
		appendBlock(sb, block, "");
	}

	public void appendBlock(StringBuilder sb, Statement[] block, String indent) {
		String nextIndent = indent + "    ";
		for (Statement s : block) {
			if (s instanceof Label) {
				// SF: Labels aren't on the first column anymore, they are
				// treated as pragmas if they are. Added "  "
				sb.append(indent + "  " + ((Label) s).getName() + ":" + sLinebreak);
			} else {
				appendStatement(sb, s, nextIndent);
			}
		}

	}

	public void appendStatement(StringBuilder sb, Statement s) {
		appendStatement(sb, s, "");
	}

	/**
	 * Add the string representation of the statement to the string builder.
	 * 
	 * @param sb
	 *            the string builder where the string will be appended to.
	 * @param s
	 *            the statement to print.
	 * @param indent
	 *            The current identation
	 */
	public void appendStatement(StringBuilder sb, Statement s, String indent) {
		sb.append(indent);
		if (s instanceof AssertStatement) {
			AssertStatement assertstmt = (AssertStatement) s;
			sb.append("assert ");
			appendExpression(sb, assertstmt.getFormula(), 0);
			sb.append(";");
		} else if (s instanceof AssumeStatement) {
			AssumeStatement assumestmt = (AssumeStatement) s;
			sb.append("assume ");
			appendExpression(sb, assumestmt.getFormula(), 0);
			sb.append(";");
		} else if (s instanceof HavocStatement) {
			HavocStatement havoc = (HavocStatement) s;
			sb.append("havoc ");
			String comma = "";
			for (VariableLHS id : havoc.getIdentifiers()) {
				sb.append(comma).append(id.getIdentifier());
				comma = ", ";
			}
			sb.append(";");
		} else if (s instanceof AssignmentStatement) {
			AssignmentStatement stmt = (AssignmentStatement) s;
			String comma = "";
			for (LeftHandSide lhs : stmt.getLhs()) {
				sb.append(comma);
				appendLHS(sb, lhs);
				comma = ", ";
			}
			sb.append(" := ");
			comma = "";
			for (Expression rhs : stmt.getRhs()) {
				sb.append(comma);
				appendExpression(sb, rhs, 0);
				comma = ", ";
			}
			sb.append(";");
		} else if (s instanceof CallStatement) {
			CallStatement call = (CallStatement) s;
			String comma;
			sb.append("call ");
			if (call.isForall())
				sb.append("forall ");
			if (call.getLhs().length > 0) {
				comma = "";
				for (VariableLHS lhs : call.getLhs()) {
					sb.append(comma).append(lhs.getIdentifier());
					comma = ", ";
				}
				sb.append(" := ");
			}
			sb.append(call.getMethodName());
			sb.append("(");
			comma = "";
			for (Expression arg : call.getArguments()) {
				sb.append(comma);
				appendExpression(sb, arg, 0);
				comma = ", ";
			}
			sb.append(");");
		} else if (s instanceof BreakStatement) {
			String label = ((BreakStatement) s).getLabel();
			sb.append("break");
			if (label != null)
				sb.append(" ").append(label);
			sb.append(";");
		} else if (s instanceof ReturnStatement) {
			sb.append("return;");
		} else if (s instanceof GotoStatement) {
			sb.append("goto ");
			String comma = "";
			for (String label : ((GotoStatement) s).getLabels()) {
				sb.append(comma).append(label);
				comma = ", ";
			}
			sb.append(";");
		} else if (s instanceof IfStatement) {
			IfStatement stmt = (IfStatement) s;
			Statement[] elsePart;
			while (true) {
				sb.append("if (");
				appendExpression(sb, stmt.getCondition(), 0);
				sb.append(") {" + sLinebreak);
				appendBlock(sb, stmt.getThenPart(), indent);
				sb.append(indent).append("}");
				elsePart = stmt.getElsePart();
				if (elsePart.length != 1 || !(elsePart[0] instanceof IfStatement))
					break;
				stmt = (IfStatement) elsePart[0];
				sb.append(" else ");
			}
			if (elsePart.length > 0) {
				sb.append(" else {" + sLinebreak);
				appendBlock(sb, stmt.getElsePart(), indent);
				sb.append(indent).append("}");
			}
		} else if (s instanceof WhileStatement) {
			WhileStatement stmt = (WhileStatement) s;
			sb.append("while (");
			appendExpression(sb, stmt.getCondition(), 0);
			sb.append(")" + sLinebreak);
			for (LoopInvariantSpecification spec : stmt.getInvariants()) {
				sb.append(indent).append("    ");
				if (spec.isFree()) {
					sb.append("free ");
				}
				sb.append("invariant ");
				appendExpression(sb, spec.getFormula(), 0);
				sb.append(";" + sLinebreak);
			}
			sb.append(indent).append("{" + sLinebreak);
			appendBlock(sb, stmt.getBody(), indent);
			sb.append(indent).append("}");
		} else if (s instanceof Label) {
			sb.append(((Label) s).getName()).append(":");
		} else {
			throw new IllegalArgumentException(s.toString());
		}
		sb.append(sLinebreak);
	}

	/**
	 * Print statement.
	 * 
	 * @param s
	 *            the statement to print.
	 * @param indent
	 *            the current indent level.
	 */
	public void printStatement(Statement s, String indent) {
		StringBuilder sb = new StringBuilder();
		appendStatement(sb, s, indent);
		m_Writer.print(sb.toString());
	}

	/**
	 * Append left hand side.
	 * 
	 * @param sb
	 *            the StringBuilder to append to.
	 * @param lhs
	 *            the left hand side
	 */
	private void appendLHS(StringBuilder sb, LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			sb.append(((VariableLHS) lhs).getIdentifier());
		} else if (lhs instanceof ArrayLHS) {
			ArrayLHS arrlhs = (ArrayLHS) lhs;
			appendLHS(sb, arrlhs.getArray());
			sb.append("[");
			String comma = "";
			for (Expression index : arrlhs.getIndices()) {
				sb.append(comma);
				appendExpression(sb, index, 0);
				comma = ",";
			}
			sb.append("]");
		} else if (lhs instanceof StructLHS) {
			StructLHS strlhs = (StructLHS) lhs;
			appendLHS(sb, strlhs.getStruct());
			sb.append("!");
			sb.append(strlhs.getField());
		} else {
			throw new IllegalArgumentException(lhs.toString());
		}
	}

	/**
	 * Print Axiom.
	 * 
	 * @param decl
	 *            the axiom to print.
	 */
	public void printAxiom(Axiom decl) {
		StringBuilder sb = new StringBuilder();
		sb.append("axiom ");
		appendAttributes(sb, decl.getAttributes());
		appendExpression(sb, decl.getFormula(), 0);
		sb.append(";");
		m_Writer.println(sb.toString());
	}

	/**
	 * Print variable declaration.
	 * 
	 * @param decl
	 *            the variable declaration to print.
	 * @param indent
	 *            the current indent level.
	 */
	public void printVarDeclaration(VariableDeclaration decl, String indent) {
		StringBuilder sb = new StringBuilder();
		appendVariableDeclaration(sb, decl, indent);
		m_Writer.print(sb.toString());
	}

	protected void appendVariableDeclaration(StringBuilder sb, VariableDeclaration decl, String indent) {
		sb.append(indent).append("var ");
		appendAttributes(sb, decl.getAttributes());
		appendVarList(sb, decl.getVariables());
		sb.append(";");
		sb.append(sLinebreak);
	}

	public void appendVariableDeclaration(StringBuilder sb, VariableDeclaration decl) {
		appendVariableDeclaration(sb, decl, "");
	}

	/**
	 * Print constant declaration.
	 * 
	 * @param decl
	 *            the constant declaration to print.
	 */
	public void printConstDeclaration(ConstDeclaration decl) {
		StringBuilder sb = new StringBuilder();
		sb.append("const ");
		appendAttributes(sb, decl.getAttributes());
		if (decl.isUnique())
			sb.append("unique ");
		appendVarList(sb, new VarList[] { decl.getVarList() });
		if (decl.getParentInfo() != null) {
			sb.append(" <:");
			String comma = " ";
			for (ParentEdge edge : decl.getParentInfo()) {
				sb.append(comma);
				if (edge.isUnique())
					sb.append("unique ");
				sb.append(edge.getIdentifier());
				comma = ", ";
			}
		}
		if (decl.isComplete())
			sb.append(" complete");
		sb.append(";");
		m_Writer.println(sb.toString());
	}
}
