/*
 * Copyright (C) 2008-2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2008-2016 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 *
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck.CheckableExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ParentEdge;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.FunctionSignature;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.StructType;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * This class is a AST-Visitor for creating textual representations of the tree. It creates a String.
 *
 * @author Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 */
public class TypeChecker extends BaseObserver {
	private TypeManager mTypeManager;
	private HashMap<String, FunctionInfo> mDeclaredFunctions;
	private HashMap<String, ProcedureInfo> mDeclaredProcedures;
	private HashMap<String, VariableInfo> mDeclaredVars;
	private ScopedHashMap<String, VariableInfo> mVarScopes;

	/**
	 * Maps a procedure identifier to all variables that occur in a modifies clause of this procedure.
	 */
	private final Map<String, Set<String>> mProc2ModfiedGlobals = new HashMap<>();

	/**
	 * Identifier of procedure that is checked at the moment.
	 */
	private String mCurrentProcedure;

	/**
	 * Identifiers of global variables
	 */
	private final Set<String> mGlobals = new HashSet<>();

	/**
	 * Identifiers of the in-parameters of the checked procedure
	 */
	private Set<String> mInParams;

	/**
	 * Identifiers of the out-parameters of the checked procedure
	 */
	private Set<String> mOutParams;

	/**
	 * Identifiers of the local variables of the checked procedure
	 */
	private Set<String> mLocalVars;
	private final IUltimateServiceProvider mServices;

	public TypeChecker(final IUltimateServiceProvider services) {
		mServices = services;
	}

	private static int getBitVecLength(BoogieType t) {
		t = t.getUnderlyingType();
		if (!(t instanceof PrimitiveType)) {
			return -1;
		}
		return ((PrimitiveType) t).getTypeCode();
	}

	private VariableInfo findVariable(final String name) {
		final VariableInfo rtr = mVarScopes.get(name);
		if (rtr == null) {
			return mDeclaredVars.get(name);
		}
		return rtr;
	}

	private BoogieType typecheckExpression(final Expression expr) {
		BoogieType resultType;
		if (expr instanceof BinaryExpression) {
			final BinaryExpression binexp = (BinaryExpression) expr;
			BoogieType left = typecheckExpression(binexp.getLeft());
			BoogieType right = typecheckExpression(binexp.getRight());

			switch (binexp.getOperator()) {
			case LOGICIFF:
			case LOGICIMPLIES:
			case LOGICAND:
			case LOGICOR:
				if (!left.equals(BoogieType.TYPE_ERROR) && !left.equals(BoogieType.TYPE_BOOL)
						|| !right.equals(BoogieType.TYPE_ERROR) && !right.equals(BoogieType.TYPE_BOOL)) {
					typeError(expr, "Type check failed for " + expr);
				}
				resultType = BoogieType.TYPE_BOOL; /* try to recover in any case */
				break;
			case ARITHDIV:
			case ARITHMINUS:
			case ARITHMOD:
			case ARITHMUL:
			case ARITHPLUS:
				/* Try to recover for error types */
				if (left.equals(BoogieType.TYPE_ERROR)) {
					left = right;
				} else if (right.equals(BoogieType.TYPE_ERROR)) {
					right = left;
				}
				if (!left.equals(right) || !left.equals(BoogieType.TYPE_INT) && !left.equals(BoogieType.TYPE_REAL)
						|| left.equals(BoogieType.TYPE_REAL)
								&& binexp.getOperator() == BinaryExpression.Operator.ARITHMOD) {
					typeError(expr, "Type check failed for " + expr);
					resultType = BoogieType.TYPE_ERROR;
				} else {
					resultType = left;
				}
				break;
			case COMPLT:
			case COMPGT:
			case COMPLEQ:
			case COMPGEQ:
				/* Try to recover for error types */
				if (left.equals(BoogieType.TYPE_ERROR)) {
					left = right;
				} else if (right.equals(BoogieType.TYPE_ERROR)) {
					right = left;
				}
				if (!left.equals(right) || !left.equals(BoogieType.TYPE_INT) && !left.equals(BoogieType.TYPE_REAL)) {
					typeError(expr, "Type check failed for " + expr);
				}
				resultType = BoogieType.TYPE_BOOL; /* try to recover in any case */
				break;
			case COMPNEQ:
			case COMPEQ:
				if (!left.isUnifiableTo(right)) {
					typeError(expr, "Type check failed for " + expr);
				}
				resultType = BoogieType.TYPE_BOOL; /* try to recover in any case */
				break;
			case COMPPO:
				if (!left.equals(right) && !left.equals(BoogieType.TYPE_ERROR)
						&& !right.equals(BoogieType.TYPE_ERROR)) {
					typeError(expr, "Type check failed for " + expr + ": " + left.getUnderlyingType() + " != "
							+ right.getUnderlyingType());
				}
				resultType = BoogieType.TYPE_BOOL; /* try to recover in any case */
				break;
			case BITVECCONCAT:
				int leftLen = getBitVecLength(left);
				int rightLen = getBitVecLength(right);
				if (leftLen < 0 || rightLen < 0 || leftLen + rightLen < 0 /*
																			 * handle overflow
																			 */) {
					if (!left.equals(BoogieType.TYPE_ERROR) && !right.equals(BoogieType.TYPE_ERROR)) {
						typeError(expr, "Type check failed for " + expr);
					}
					leftLen = 0;
					rightLen = 0; /* recover */
				}
				resultType = BoogieType.createBitvectorType(leftLen + rightLen);
				break;
			default:
				internalError("Unknown Binary operator " + binexp.getOperator());
				resultType = BoogieType.TYPE_ERROR;
				break;
			}
		} else if (expr instanceof UnaryExpression) {
			final UnaryExpression unexp = (UnaryExpression) expr;
			final BoogieType subtype = typecheckExpression(unexp.getExpr());
			switch (unexp.getOperator()) {
			case LOGICNEG:
				if (!subtype.equals(BoogieType.TYPE_ERROR) && !subtype.equals(BoogieType.TYPE_BOOL)) {
					typeError(expr, "Type check failed for " + expr);
				}
				resultType = BoogieType.TYPE_BOOL; /* try to recover in any case */
				break;
			case ARITHNEGATIVE:
				if (!subtype.equals(BoogieType.TYPE_ERROR) && !subtype.equals(BoogieType.TYPE_INT)
						&& !subtype.equals(BoogieType.TYPE_REAL)) {
					typeError(expr, "Type check failed for " + expr);
				}
				resultType = subtype;
				break;
			case OLD:
				resultType = subtype;
				break;
			default:
				internalError("Unknown Unary operator " + unexp.getOperator());
				resultType = BoogieType.TYPE_ERROR;
				break;
			}
		} else if (expr instanceof BitVectorAccessExpression) {
			final BitVectorAccessExpression bvaexpr = (BitVectorAccessExpression) expr;
			final BoogieType bvType = typecheckExpression(bvaexpr.getBitvec());
			final int bvlen = getBitVecLength(bvType);
			int end = bvaexpr.getEnd();
			int start = bvaexpr.getStart();
			if (start < 0 || end < start || bvlen < end) {
				if (!bvType.equals(BoogieType.TYPE_ERROR)) {
					typeError(expr, "Type check failed for " + expr);
				}
				start = end = 0;
			}
			resultType = BoogieType.createBitvectorType(end - start);
		} else if (expr instanceof StructAccessExpression) {
			final StructAccessExpression sae = (StructAccessExpression) expr;
			final BoogieType e = typecheckExpression(sae.getStruct()).getUnderlyingType();
			if (!(e instanceof StructType)) {
				if (!e.equals(BoogieType.TYPE_ERROR)) {
					typeError(expr, "Type check failed (not a struct): " + expr);
				}
				resultType = BoogieType.TYPE_ERROR;
			} else {
				final StructType str = (StructType) e;
				resultType = null;
				for (int i = 0; i < str.getFieldCount(); i++) {
					if (str.getFieldIds()[i].equals(sae.getField())) {
						resultType = str.getFieldType(i);
					}
				}
				if (resultType == null) {
					typeError(expr, "Type check failed (field " + sae.getField() + " not in struct): " + expr);
					resultType = BoogieType.TYPE_ERROR;
				}
			}
		} else if (expr instanceof ArrayAccessExpression) {
			final ArrayAccessExpression aaexpr = (ArrayAccessExpression) expr;
			final BoogieType e = typecheckExpression(aaexpr.getArray()).getUnderlyingType();
			if (!(e instanceof ArrayType)) {
				if (!e.equals(BoogieType.TYPE_ERROR)) {
					typeError(expr, "Type check failed (not an array): " + expr);
				}
				resultType = BoogieType.TYPE_ERROR;
			} else {
				final ArrayType arr = (ArrayType) e;
				final BoogieType[] subst = new BoogieType[arr.getNumPlaceholders()];
				final Expression[] indices = aaexpr.getIndices();
				if (indices.length != arr.getIndexCount()) {
					typeError(expr, "Type check failed (wrong number of indices): " + expr);
				} else {
					for (int i = 0; i < indices.length; i++) {
						final BoogieType t = typecheckExpression(indices[i]);
						if (!t.equals(BoogieType.TYPE_ERROR) && !arr.getIndexType(i).unify(t, subst)) {
							typeError(expr, "Type check failed (index " + i + "): " + expr);
						}
					}
				}
				resultType = arr.getValueType().substitutePlaceholders(subst);
			}
		} else if (expr instanceof ArrayStoreExpression) {
			final ArrayStoreExpression asexpr = (ArrayStoreExpression) expr;
			final BoogieType e = typecheckExpression(asexpr.getArray()).getUnderlyingType();
			if (!(e instanceof ArrayType)) {
				if (!e.equals(BoogieType.TYPE_ERROR)) {
					typeError(expr, "Type check failed (not an array): " + expr);
				}
				resultType = BoogieType.TYPE_ERROR;
			} else {
				final ArrayType arr = (ArrayType) e;
				final BoogieType[] subst = new BoogieType[arr.getNumPlaceholders()];
				final Expression[] indices = asexpr.getIndices();
				if (indices.length != arr.getIndexCount()) {
					typeError(expr, "Type check failed (wrong number of indices): " + expr);
				} else {
					for (int i = 0; i < indices.length; i++) {
						final BoogieType t = typecheckExpression(indices[i]);
						if (!t.equals(BoogieType.TYPE_ERROR) && !arr.getIndexType(i).unify(t, subst)) {
							typeError(expr, "Type check failed (index " + i + "): " + expr);
						}
					}
					final BoogieType valueType = typecheckExpression(asexpr.getValue());
					if (!valueType.equals(BoogieType.TYPE_ERROR) && !arr.getValueType().unify(valueType, subst)) {
						typeError(expr, "Type check failed (value): " + expr);
					}
				}
				resultType = arr;
			}
		} else if (expr instanceof BooleanLiteral) {
			resultType = BoogieType.TYPE_BOOL;
		} else if (expr instanceof IntegerLiteral) {
			resultType = BoogieType.TYPE_INT;
		} else if (expr instanceof RealLiteral) {
			resultType = BoogieType.TYPE_REAL;
		} else if (expr instanceof BitvecLiteral) {
			final BitvecLiteral bvlit = (BitvecLiteral) expr;
			resultType = BoogieType.createBitvectorType(bvlit.getLength());
		} else if (expr instanceof StructConstructor) {
			final StructConstructor struct = (StructConstructor) expr;
			final Expression[] fieldExprs = struct.getFieldValues();
			final BoogieType[] fieldTypes = new BoogieType[fieldExprs.length];
			boolean hasError = false;
			for (int i = 0; i < fieldExprs.length; i++) {
				fieldTypes[i] = typecheckExpression(fieldExprs[i]);
				hasError |= fieldTypes[i] == BoogieType.TYPE_ERROR;
			}
			resultType = hasError ? BoogieType.TYPE_ERROR
					: BoogieType.createStructType(struct.getFieldIdentifiers(), fieldTypes);
		} else if (expr instanceof IdentifierExpression) {
			final IdentifierExpression idexpr = (IdentifierExpression) expr;
			final String name = idexpr.getIdentifier();
			final VariableInfo info = findVariable(name);
			if (info == null) {
				typeError(expr, "Undeclared identifier " + name + " in " + expr);
				resultType = BoogieType.TYPE_ERROR;
			} else {
				final DeclarationInformation declInfo = idexpr.getDeclarationInformation();
				if (declInfo == null) {
					idexpr.setDeclarationInformation(info.getDeclarationInformation());
				} else {
					checkExistingDeclarationInformation(name, declInfo, info.getDeclarationInformation());
				}
				resultType = info.getType().getUnderlyingType();
			}
		} else if (expr instanceof FunctionApplication) {
			final FunctionApplication app = (FunctionApplication) expr;
			final String name = app.getIdentifier();
			final FunctionInfo fi = mDeclaredFunctions.get(name);
			if (fi == null) {
				typeError(expr, "Undeclared function " + name + " in " + expr);
				resultType = BoogieType.TYPE_ERROR;
			} else {
				final FunctionSignature fs = fi.getSignature();
				final BoogieType[] subst = new BoogieType[fs.getTypeArgCount()];
				final Expression[] appArgs = app.getArguments();
				if (appArgs.length != fs.getParamCount()) {
					typeError(expr, "Type check failed (wrong number of indices): " + expr);
				} else {
					for (int i = 0; i < appArgs.length; i++) {
						final BoogieType t = typecheckExpression(appArgs[i]);
						if (!t.equals(BoogieType.TYPE_ERROR) && !fs.getParamType(i).unify(t, subst)) {
							typeError(expr, "Type check failed (index " + i + "): " + expr);
						}
					}
				}
				resultType = fs.getResultType().substitutePlaceholders(subst);
			}
		} else if (expr instanceof IfThenElseExpression) {
			final IfThenElseExpression ite = (IfThenElseExpression) expr;
			final BoogieType condType = typecheckExpression(ite.getCondition());
			if (!condType.equals(BoogieType.TYPE_ERROR) && !condType.equals(BoogieType.TYPE_BOOL)) {
				typeError(expr, "if expects boolean type: " + expr);
			}
			final BoogieType left = typecheckExpression(ite.getThenPart());
			final BoogieType right = typecheckExpression(ite.getElsePart());
			if (!left.isUnifiableTo(right)) {
				typeError(expr, "Type check failed for " + expr);
				resultType = BoogieType.TYPE_ERROR;
			} else {
				resultType = left.equals(BoogieType.TYPE_ERROR) ? right : left;
			}
		} else if (expr instanceof QuantifierExpression) {
			final QuantifierExpression quant = (QuantifierExpression) expr;
			final TypeParameters typeParams = new TypeParameters(quant.getTypeParams());
			mTypeManager.pushTypeScope(typeParams);

			final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.QUANTIFIED, null);
			final VarList[] parameters = quant.getParameters();

			mVarScopes.beginScope();
			for (final VarList p : parameters) {
				final BoogieType type = mTypeManager.resolveType(p.getType());
				for (final String id : p.getIdentifiers()) {
					mVarScopes.put(id, new VariableInfo(true, null, id, type, declInfo));
				}
			}
			if (!typeParams.fullyUsed()) {
				typeError(expr, "Type args not fully used in variable types: " + expr);
			}

			typecheckAttributes(quant.getAttributes());
			final BoogieType t = typecheckExpression(quant.getSubformula());
			if (!t.equals(BoogieType.TYPE_ERROR) && !t.equals(BoogieType.TYPE_BOOL)) {
				typeError(expr, "Type check error in: " + expr);
			}
			mVarScopes.endScope();
			mTypeManager.popTypeScope();
			resultType = BoogieType.TYPE_BOOL;
		} else if (expr instanceof WildcardExpression) {
			resultType = BoogieType.TYPE_BOOL;
		} else {
			throw new IllegalStateException("Unknown expression node " + expr);
		}
		expr.setType(resultType);
		return resultType;
	}

	/**
	 * Compare existingDeclInfo with correctDeclInfo and raise an internalError if both are not equivalent.
	 */
	private static void checkExistingDeclarationInformation(final String id,
			final DeclarationInformation existingDeclInfo, final DeclarationInformation correctDeclInfo) {
		if (!existingDeclInfo.equals(correctDeclInfo)) {
			internalError("Incorrect DeclarationInformation of " + id + ". Expected: " + correctDeclInfo + "   Found: "
					+ existingDeclInfo);
		}
	}

	private BoogieType typecheckLeftHandSide(final LeftHandSide lhs) {
		BoogieType resultType;
		if (lhs instanceof VariableLHS) {
			final VariableLHS vLhs = (VariableLHS) lhs;
			final String name = vLhs.getIdentifier();
			resultType = checkVarModification(lhs, name);
			final VariableInfo info = findVariable(name);
			if (info != null) {
				final DeclarationInformation declInfo = vLhs.getDeclarationInformation();
				if (declInfo == null) {
					vLhs.setDeclarationInformation(info.getDeclarationInformation());
				} else {
					checkExistingDeclarationInformation(name, declInfo, info.getDeclarationInformation());
				}
			}
		} else if (lhs instanceof StructLHS) {
			final StructLHS slhs = (StructLHS) lhs;
			final BoogieType type = typecheckLeftHandSide(slhs.getStruct()).getUnderlyingType();
			if (!(type instanceof StructType)) {
				if (!type.equals(BoogieType.TYPE_ERROR)) {
					typeError(lhs, "Type check failed (not a struct): " + lhs);
				}
				resultType = BoogieType.TYPE_ERROR;
			} else {
				final StructType str = (StructType) type;
				resultType = null;
				for (int i = 0; i < str.getFieldCount(); i++) {
					if (str.getFieldIds()[i].equals(slhs.getField())) {
						resultType = str.getFieldType(i);
					}
				}
				if (resultType == null) {
					typeError(lhs, "Type check failed (field " + slhs.getField() + " not in struct): " + lhs);
					resultType = BoogieType.TYPE_ERROR;
				}
			}
		} else if (lhs instanceof ArrayLHS) {
			final ArrayLHS alhs = (ArrayLHS) lhs;
			// SFA: Patched to look inside ConstructedType
			final BoogieType type = typecheckLeftHandSide(alhs.getArray()).getUnderlyingType();
			if (!(type instanceof ArrayType)) {
				if (!type.equals(BoogieType.TYPE_ERROR)) {
					typeError(lhs, "Type check failed (not an array): " + lhs);
				}
				resultType = BoogieType.TYPE_ERROR;
			} else {
				final ArrayType arrType = (ArrayType) type;
				final BoogieType[] subst = new BoogieType[arrType.getNumPlaceholders()];
				final Expression[] indices = alhs.getIndices();
				if (indices.length != arrType.getIndexCount()) {
					typeError(lhs, "Type check failed (wrong number of indices): " + lhs);
					resultType = BoogieType.TYPE_ERROR;
				} else {
					for (int i = 0; i < indices.length; i++) {
						final BoogieType t = typecheckExpression(indices[i]);
						if (!t.equals(BoogieType.TYPE_ERROR) && !arrType.getIndexType(i).unify(t, subst)) {
							typeError(lhs, "Type check failed (index " + i + "): " + lhs);
						}
					}
					resultType = arrType.getValueType().substitutePlaceholders(subst);
				}
			}
		} else {
			internalError("Unknown LHS: " + lhs);
			resultType = BoogieType.TYPE_ERROR;
		}
		lhs.setType(resultType);
		return resultType;
	}

	private void typecheckAttributes(final Attribute[] attributes) {
		for (final Attribute attr : attributes) {
			Expression[] exprs;
			if (attr instanceof Trigger) {
				exprs = ((Trigger) attr).getTriggers();
			} else if (attr instanceof NamedAttribute) {
				exprs = ((NamedAttribute) attr).getValues();
			} else {
				throw new IllegalStateException("Unknown Attribute " + attr);
			}
			for (final Expression e : exprs) {
				if (!(e instanceof StringLiteral)) {
					typecheckExpression(e);
				}
			}
		}
	}

	private static String getLeftHandSideIdentifier(LeftHandSide lhs) {
		while (lhs instanceof ArrayLHS || lhs instanceof StructLHS) {
			if (lhs instanceof ArrayLHS) {
				lhs = ((ArrayLHS) lhs).getArray();
			} else if (lhs instanceof StructLHS) {
				lhs = ((StructLHS) lhs).getStruct();
			}
		}
		return ((VariableLHS) lhs).getIdentifier();
	}

	private void processVariableDeclaration(final VariableDeclaration varDecl) {
		final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.GLOBAL, null);
		for (final VarList varlist : varDecl.getVariables()) {
			final BoogieType type = mTypeManager.resolveType(varlist.getType());
			for (final String id : varlist.getIdentifiers()) {
				mDeclaredVars.put(id, new VariableInfo(false, varDecl, id, type, declInfo));
				mGlobals.add(id);
			}
		}
	}

	private void processConstDeclaration(final ConstDeclaration constDecl) {
		final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.GLOBAL, null);
		final VarList varList = constDecl.getVarList();
		final BoogieType type = mTypeManager.resolveType(varList.getType());
		for (final String id : varList.getIdentifiers()) {
			mDeclaredVars.put(id, new VariableInfo(true, constDecl, id, type, declInfo));
		}
	}

	private void checkConstDeclaration(final ConstDeclaration constDecl) {
		final ParentEdge[] parents = constDecl.getParentInfo();
		if (parents == null) {
			return;
		}
		final BoogieType type = (BoogieType) constDecl.getVarList().getType().getBoogieType();
		for (final ParentEdge p : parents) {
			final VariableInfo var = mDeclaredVars.get(p.getIdentifier());
			if (var == null || !var.isRigid()) {
				typeError(constDecl, constDecl + ": parent is not a const");
			} else if (!type.equals(var.getType()) && !var.getType().equals(BoogieType.TYPE_ERROR)
					&& !type.equals(BoogieType.TYPE_ERROR)) {
				typeError(constDecl, constDecl + ": parent is not of same type");
			}
		}
	}

	private void processFunctionDeclaration(final FunctionDeclaration funcDecl) {
		final String name = funcDecl.getIdentifier();

		final TypeParameters typeParams = new TypeParameters(funcDecl.getTypeParams());
		mTypeManager.pushTypeScope(typeParams);

		final VarList[] paramNodes = funcDecl.getInParams();
		final String[] paramNames = new String[paramNodes.length];
		final BoogieType[] paramTypes = new BoogieType[paramNodes.length];
		for (int i = 0; i < paramNodes.length; i++) {
			final String[] names = paramNodes[i].getIdentifiers();
			if (names.length > 0) {
				paramNames[i] = names[0];
			}
			paramTypes[i] = mTypeManager.resolveType(paramNodes[i].getType());
		}
		if (!typeParams.fullyUsed()) {
			typeError(funcDecl, "Type args not fully used in function parameter: " + funcDecl);
		}

		String valueName = null;
		final String[] valueNames = funcDecl.getOutParam().getIdentifiers();
		final BoogieType valueType = mTypeManager.resolveType(funcDecl.getOutParam().getType());
		if (valueNames.length > 0) {
			valueName = valueNames[0];
		}

		mTypeManager.popTypeScope();

		final FunctionSignature fs =
				new FunctionSignature(funcDecl.getTypeParams().length, paramNames, paramTypes, valueName, valueType);
		mDeclaredFunctions.put(name, new FunctionInfo(funcDecl, name, typeParams, fs));
	}

	private void processFunctionDefinition(final FunctionDeclaration funcDecl) {
		/* type check the body of a function */
		if (funcDecl.getBody() == null) {
			return;
		}

		/* Declare local variables for parameters */
		final String name = funcDecl.getIdentifier();
		final FunctionInfo fi = mDeclaredFunctions.get(name);
		final TypeParameters typeParams = fi.getTypeParameters();

		final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, name);
		mTypeManager.pushTypeScope(typeParams);
		final FunctionSignature fs = fi.getSignature();
		mVarScopes.beginScope();
		final int paramCount = fs.getParamCount();
		for (int i = 0; i < paramCount; i++) {
			final String paramName = fs.getParamName(i);
			if (paramName != null) {
				mVarScopes.put(paramName,
						new VariableInfo(true, null, fs.getParamName(i), fs.getParamType(i), declInfo));
			}
		}
		final BoogieType valueType = typecheckExpression(funcDecl.getBody());
		if (!valueType.equals(BoogieType.TYPE_ERROR) && !valueType.equals(fs.getResultType())) {
			typeError(funcDecl, "Return type of function doesn't match body");
		}
		mVarScopes.endScope();
		mTypeManager.popTypeScope();
	}

	/**
	 * TODO : some meaningful description ...
	 *
	 * @param proc
	 *            the procedure to process.
	 */
	public void processProcedureDeclaration(final Procedure proc) {
		if (proc.getSpecification() == null) {
			/* This is only an implementation. It is checked later. */
			return;
		}

		final String name = proc.getIdentifier();
		final TypeParameters typeParams = new TypeParameters(proc.getTypeParams());
		mTypeManager.pushTypeScope(typeParams);

		final DeclarationInformation declInfoInParam =
				new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, proc.getIdentifier());
		final LinkedList<VariableInfo> inParams = new LinkedList<>();
		for (final VarList vl : proc.getInParams()) {
			final BoogieType type = mTypeManager.resolveType(vl.getType());
			for (final String id : vl.getIdentifiers()) {
				inParams.add(new VariableInfo(true /* in params are rigid */, proc, id, type, declInfoInParam));
			}
		}
		if (!typeParams.fullyUsed()) {
			typeError(proc, "Type args not fully used in procedure parameter: " + proc);
		}
		final DeclarationInformation declInfoOutParam =
				new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, proc.getIdentifier());
		final LinkedList<VariableInfo> outParams = new LinkedList<>();
		for (final VarList vl : proc.getOutParams()) {
			final BoogieType type = mTypeManager.resolveType(vl.getType());
			for (final String id : vl.getIdentifiers()) {
				outParams.add(new VariableInfo(false, proc, id, type, declInfoOutParam));
			}
		}

		mVarScopes.beginScope();
		for (final VariableInfo vi : inParams) {
			mVarScopes.put(vi.getName(), vi);
		}
		for (final VariableInfo vi : outParams) {
			mVarScopes.put(vi.getName(), vi);
		}
		for (final VarList vl : proc.getInParams()) {
			if (vl.getWhereClause() != null) {
				final BoogieType t = typecheckExpression(vl.getWhereClause());
				if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
					typeError(vl.getWhereClause(), "Where clause is not boolean: " + vl.getWhereClause());
				}
			}
		}
		for (final VarList vl : proc.getOutParams()) {
			if (vl.getWhereClause() != null) {
				final BoogieType t = typecheckExpression(vl.getWhereClause());
				if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
					typeError(vl.getWhereClause(), "Where clause is not boolean: " + vl.getWhereClause());
				}
			}
		}
		mProc2ModfiedGlobals.put(name, new HashSet<String>());
		for (final Specification s : proc.getSpecification()) {
			if (s instanceof RequiresSpecification) {
				final BoogieType t = typecheckExpression(((RequiresSpecification) s).getFormula());
				if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
					typeError(s, "Requires clause is not boolean: " + s);
				}
			} else if (s instanceof EnsuresSpecification) {
				final BoogieType t = typecheckExpression(((EnsuresSpecification) s).getFormula());
				if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
					typeError(s, "Ensures clause is not boolean: " + s);
				}
			} else if (s instanceof ModifiesSpecification) {
				final Set<String> modifiedGlobals = mProc2ModfiedGlobals.get(name);
				for (final VariableLHS var : ((ModifiesSpecification) s).getIdentifiers()) {
					final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.GLOBAL, null);
					if (var.getDeclarationInformation() == null) {
						var.setDeclarationInformation(declInfo);
					} else {
						checkExistingDeclarationInformation(var.getIdentifier(), var.getDeclarationInformation(),
								declInfo);
					}
					final String id = var.getIdentifier();
					if (mGlobals.contains(id)) {
						modifiedGlobals.add(id);
						var.setType(findVariable(id).getType());
					} else {
						typeError(s, "Modifies clause contains " + id + " which is not a global variable");
					}
				}
			} else {
				internalError("Unknown Procedure specification: " + s);
			}
		}
		mVarScopes.endScope();
		mTypeManager.popTypeScope();

		final ProcedureInfo pi =
				new ProcedureInfo(proc, typeParams, inParams.toArray(new VariableInfo[inParams.size()]),
						outParams.toArray(new VariableInfo[outParams.size()]));
		mDeclaredProcedures.put(name, pi);
	}

	/**
	 * Collect all labels in the given block and store them in the hash set labels.
	 *
	 * @param labels
	 *            The hash set where the labels are stored.
	 * @param block
	 *            The code block.
	 */
	private void processLabels(final HashSet<String> labels, final Statement[] block) {
		for (final Statement s : block) {
			if (s instanceof Label) {
				labels.add(((Label) s).getName());
			} else if (s instanceof IfStatement) {
				processLabels(labels, ((IfStatement) s).getThenPart());
				processLabels(labels, ((IfStatement) s).getElsePart());
			} else if (s instanceof WhileStatement) {
				processLabels(labels, ((WhileStatement) s).getBody());
			}
		}
	}

	/**
	 * Type check the given statement.
	 *
	 * @param outer
	 *            the labels right before some outer block.
	 * @param allLabels
	 *            all labels appearing in the implementation body.
	 * @param statement
	 *            the code to type check.
	 */
	private void typecheckStatement(final Stack<String> outer, final HashSet<String> allLabels,
			final Statement statement) {
		if (statement instanceof AssumeStatement) {
			final BoogieType t = typecheckExpression(((AssumeStatement) statement).getFormula());
			if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
				typeError(statement, "Assume is not boolean: " + statement);
			}
		} else if (statement instanceof AssertStatement) {
			final BoogieType t = typecheckExpression(((AssertStatement) statement).getFormula());
			if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
				typeError(statement, "Assert is not boolean: " + statement);
			}
		} else if (statement instanceof BreakStatement) {
			final String label = ((BreakStatement) statement).getLabel();
			if (!outer.contains(label == null ? "*" : label)) {
				typeError(statement, "Break label not found: " + statement);
			}
		} else if (statement instanceof HavocStatement) {
			for (final VariableLHS id : ((HavocStatement) statement).getIdentifiers()) {
				typecheckLeftHandSide(id);
			}
		} else if (statement instanceof AssignmentStatement) {
			final AssignmentStatement astmt = (AssignmentStatement) statement;
			final LeftHandSide[] lhs = astmt.getLhs();
			final String[] lhsId = new String[lhs.length];
			final Expression[] rhs = astmt.getRhs();
			if (lhs.length != rhs.length) {
				typeError(statement, "Number of variables do not match in " + statement);
			} else {
				for (int i = 0; i < lhs.length; i++) {
					lhsId[i] = getLeftHandSideIdentifier(lhs[i]);
					for (int j = 0; j < i; j++) {
						if (lhsId[i].equals(lhsId[j])) {
							typeError(statement, "Variable appears multiple times in assignment: " + statement);
						}
					}
					final BoogieType lhsType = typecheckLeftHandSide(lhs[i]);
					final BoogieType rhsType = typecheckExpression(rhs[i]);
					if (!lhsType.equals(BoogieType.TYPE_ERROR) && !rhsType.equals(BoogieType.TYPE_ERROR)
							&& !lhsType.equals(rhsType)) {
						typeError(statement, "Type mismatch (" + lhsType + " != " + rhsType + ") in " + statement);
					}
				}
			}
		} else if (statement instanceof GotoStatement) {
			for (final String label : ((GotoStatement) statement).getLabels()) {
				if (!allLabels.contains(label)) {
					typeError(statement, "Goto label not found: " + statement);
				}
			}
		} else if (statement instanceof ReturnStatement) {
			/* Nothing to check */
		} else if (statement instanceof IfStatement) {
			final IfStatement ifstmt = (IfStatement) statement;
			final BoogieType t = typecheckExpression(ifstmt.getCondition());
			if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
				typeError(statement, "Condition is not boolean: " + statement);
			}
			typecheckBlock(outer, allLabels, ifstmt.getThenPart());
			typecheckBlock(outer, allLabels, ifstmt.getElsePart());
		} else if (statement instanceof WhileStatement) {
			final WhileStatement whilestmt = (WhileStatement) statement;
			final BoogieType t = typecheckExpression(whilestmt.getCondition());
			if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
				typeError(statement, "Condition is not boolean: " + statement);
			}
			for (final Specification inv : whilestmt.getInvariants()) {
				if (inv instanceof LoopInvariantSpecification) {
					typecheckExpression(((LoopInvariantSpecification) inv).getFormula());
				} else {
					internalError("Unknown while specification: " + inv);
				}
			}
			outer.push("*");
			typecheckBlock(outer, allLabels, whilestmt.getBody());
			outer.pop();
		} else if (statement instanceof CallStatement) {
			final CallStatement call = (CallStatement) statement;
			final ProcedureInfo procInfo = mDeclaredProcedures.get(call.getMethodName());
			if (procInfo == null) {
				typeError(statement, "Calling undeclared procedure " + call);
				return;
			}
			checkModifiesTransitive(call, call.getMethodName());
			if (call.isForall()) {
				final Specification[] spec = procInfo.getDeclaration().getSpecification();
				for (final Specification s : spec) {
					if (s instanceof ModifiesSpecification && !s.isFree()) {
						typeError(statement, "call forall on method with checked modifies: " + statement);
						break;
					}
				}
			}
			final BoogieType[] typeParams = new BoogieType[procInfo.getTypeParameters().getCount()];
			final VariableInfo[] inParams = procInfo.getInParams();
			final Expression[] arguments = call.getArguments();
			if (arguments.length != inParams.length) {
				typeError(statement, "Procedure called with wrong number of arguments: " + call);
				return;
			}
			for (int i = 0; i < arguments.length; i++) {
				if (call.isForall()) {
					/* check for wildcard expression and just skip them. */
					if (arguments[i] instanceof WildcardExpression) {
						arguments[i].setType(inParams[i].getType());
						continue;
					}
				}
				final BoogieType t = typecheckExpression(arguments[i]);
				if (!inParams[i].getType().unify(t, typeParams)) {
					typeError(statement, "Wrong parameter type at index " + i + ": " + call);
				}
			}
			final VariableInfo[] outParams = procInfo.getOutParams();
			final VariableLHS[] lhs = call.getLhs();
			if (lhs.length != outParams.length) {
				typeError(statement, "Number of output variables do not match in " + statement);
			} else {
				for (int i = 0; i < lhs.length; i++) {
					for (int j = 0; j < i; j++) {
						if (lhs[i].getIdentifier().equals(lhs[j].getIdentifier())) {
							typeError(statement, "Variable appears multiple times in assignment: " + statement);
						}
					}
					final BoogieType type = typecheckLeftHandSide(lhs[i]);
					if (!outParams[i].getType().unify(type, typeParams)) {
						typeError(statement, "Type mismatch (output parameter " + i + ") in " + statement);
					}
				}
			}
		} else if (statement instanceof ForkStatement) {
			// TODO: implement type checker for fork statement
			final ForkStatement fork = (ForkStatement) statement;
			final ProcedureInfo procInfo = mDeclaredProcedures.get(fork.getMethodName());
			if (procInfo == null) {
				typeError(statement, "Forking undeclared procedure " + fork);
				return;
			}
			// TODO: checkModifiesTransitives for forkStatement
			final BoogieType[] typeParams = new BoogieType[procInfo.getTypeParameters().getCount()];
			final VariableInfo[] inParams = procInfo.getInParams();
			final Expression[] arguments = fork.getArguments();
			if (arguments.length != inParams.length) {
				typeError(statement, "Procedure forked with wrong number of arguments: " + fork);
				return;
			}
			for (int i = 0; i < arguments.length; i++) {
				final BoogieType t = typecheckExpression(arguments[i]);
				if (!inParams[i].getType().unify(t, typeParams)) {
					typeError(statement, "Wrong parameter type at index " + i + ": " + fork);
				}
			}
		} else if (statement instanceof JoinStatement) {
			final JoinStatement join = (JoinStatement) statement;
			final Expression expr = join.getForkID();
			if (expr == null) {
				typeError(statement, "Expression " + expr + " does not exist.");
			}
		} else {
			internalError("Not implemented: type checking for " + statement);
		}
	}

	/**
	 * Type check the given block.
	 *
	 * @param outer
	 *            the labels right before some outer block.
	 * @param allLabels
	 *            all labels appearing in the implementation body.
	 * @param block
	 *            the code to type check.
	 */
	private void typecheckBlock(final Stack<String> outer, final HashSet<String> allLabels, final Statement[] block) {
		int numLabels = 0;
		for (final Statement s : block) {
			if (s instanceof Label) {
				outer.push(((Label) s).getName());
				numLabels++;
			} else {
				typecheckStatement(outer, allLabels, s);
				while (numLabels-- > 0) {
					outer.pop();
				}
			}
		}
	}

	/**
	 * Check if it is legal to modify variable var and if the variable was declared at all. It is not legal to modify an
	 * in-parameter of a procedure. It is not legal to modify an global variable that does not appear in the modifies
	 * clause of the procedure.
	 *
	 * @param lhs
	 *            location of the checked variable
	 * @return BoogieType of the checked variable. errorType if the variable was not declared.
	 */
	private BoogieType checkVarModification(final BoogieASTNode BoogieASTNode, final String var) {
		if (mInParams.contains(var)) {
			final String message = "Local variable " + var + " modified in " + " procedure " + mCurrentProcedure
					+ " but is an " + "in-parameter of this procedure";
			typeError(BoogieASTNode, message);
			return findVariable(var).getType();
		} else if (mOutParams.contains(var)) {
			// var is out parameter (may shadow global var), modification is
			// legal
			return findVariable(var).getType();
		} else if (mLocalVars.contains(var)) {
			// var is local variable (may shadow global var), modification is
			// legal
			return findVariable(var).getType();
		} else if (mGlobals.contains(var)) {
			final Set<String> modifiedGlobals = mProc2ModfiedGlobals.get(mCurrentProcedure);
			if (!modifiedGlobals.contains(var)) {
				final String message = "Global variable " + var + " modified in " + " procedure " + mCurrentProcedure
						+ " but not " + "contained in procedures modifies clause.";
				typeError(BoogieASTNode, message);
			}
			return findVariable(var).getType();
		} else {
			final String message =
					"Variable " + var + " modified in procedure " + mCurrentProcedure + " but not declared";
			typeError(BoogieASTNode, message);
			return BoogieType.TYPE_ERROR;
		}
	}

	/**
	 * Check if each modified variable of the called procedure is in the modifies clause of the current procedure.
	 */
	private void checkModifiesTransitive(final CallStatement call, final String callee) {
		final String caller = mCurrentProcedure;
		final Set<String> calleeModifiedGlobals = mProc2ModfiedGlobals.get(callee);
		final Set<String> callerModifiedGlobals = mProc2ModfiedGlobals.get(caller);
		for (final String var : calleeModifiedGlobals) {
			if (!callerModifiedGlobals.contains(var)) {
				final String message = "Procedure " + callee + " may modify " + var + " procedure " + caller
						+ " must not modify " + var + ". " + call + " calls " + callee + ". Modifies not transitive";
				typeError(call, message);
			}
		}
	}

	private void processBody(final Body body, final String prodecureId) {
		final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.LOCAL, prodecureId);
		mVarScopes.beginScope();
		for (final VariableDeclaration decl : body.getLocalVars()) {
			for (final VarList vl : decl.getVariables()) {
				assert vl.getType() != null : "Variable list without type";
				final BoogieType type = mTypeManager.resolveType(vl.getType());
				if (type.equals(BoogieType.TYPE_ERROR)) {
					typeError(vl, "VarList has unresolveable type " + vl.getType());
				}
				for (final String id : vl.getIdentifiers()) {
					checkIfAlreadyInOutLocal(vl, id);
					mLocalVars.add(id);
					mVarScopes.put(id, new VariableInfo(false, decl, id, type, declInfo));
				}
			}
		}

		/* Now check where clauses */
		for (final VariableDeclaration decl : body.getLocalVars()) {
			for (final VarList vl : decl.getVariables()) {
				if (vl.getWhereClause() != null) {
					final BoogieType t = typecheckExpression(vl.getWhereClause());
					if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
						typeError(vl.getWhereClause(), "Where clause is not boolean: " + decl);
					}
				}
			}
		}

		/* Get Labels */
		final HashSet<String> labels = new HashSet<>();
		processLabels(labels, body.getBlock());
		/* Finally check statements */
		typecheckBlock(new Stack<String>(), labels, body.getBlock());
		mVarScopes.endScope();
	}

	private void processImplementation(final Procedure impl) {
		if (impl.getBody() == null) {
			/* This is a procedure declaration without body. Nothing to check. */
			return;
		}
		final ProcedureInfo procInfo = mDeclaredProcedures.get(impl.getIdentifier());
		if (procInfo == null) {
			typeError(impl, "Implementation without procedure: " + impl.getIdentifier());
			return;
		}
		final TypeParameters typeParams = new TypeParameters(impl.getTypeParams());
		mTypeManager.pushTypeScope(typeParams);

		mCurrentProcedure = impl.getIdentifier();
		mInParams = new HashSet<>();
		mOutParams = new HashSet<>();
		mLocalVars = new HashSet<>();
		DeclarationInformation declInfoInParam;
		DeclarationInformation declInfoOutParam;
		// We call this procedure object a pure implementation if it contains
		// only the implementation and another procedure object contains the
		// specification
		final boolean isPureImplementation = procInfo.getDeclaration() != impl;
		if (isPureImplementation) {
			declInfoInParam = new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, impl.getIdentifier());
			declInfoOutParam = new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM, impl.getIdentifier());
		} else {
			declInfoInParam = new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, impl.getIdentifier());
			declInfoOutParam = new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, impl.getIdentifier());
		}
		mVarScopes.beginScope();
		final VariableInfo[] procInParams = procInfo.getInParams();
		final VariableInfo[] procOutParams = procInfo.getOutParams();
		int i = 0;
		for (final VarList vl : impl.getInParams()) {
			final BoogieType type = mTypeManager.resolveType(vl.getType());
			for (final String id : vl.getIdentifiers()) {
				if (i >= procInParams.length) {
					typeError(vl, "Too many input parameters in " + impl);
				} else if (!procInParams[i++].getType().equals(type)) {
					typeError(vl, "Type differs at parameter " + id + " in " + impl);
				}
				checkIfAlreadyInOutLocal(vl, id);
				mInParams.add(id);
				mVarScopes.put(id, new VariableInfo(true /* in params are rigid */, impl, id, type, declInfoInParam));
			}
		}
		if (i < procInParams.length) {
			typeError(impl, "Too few input parameters in " + impl);
		}
		if (!typeParams.fullyUsed()) {
			typeError(impl, "Type args not fully used in implementation: " + impl);
		}
		i = 0;
		for (final VarList vl : impl.getOutParams()) {
			final BoogieType type = mTypeManager.resolveType(vl.getType());
			for (final String id : vl.getIdentifiers()) {
				if (i >= procOutParams.length) {
					typeError(vl, "Too many output parameters in " + impl);
				} else if (!procOutParams[i++].getType().equals(type)) {
					typeError(vl, "Type differs at parameter " + id + " in " + impl);
				}
				checkIfAlreadyInOutLocal(vl, id);
				mOutParams.add(id);
				mVarScopes.put(id, new VariableInfo(false, impl, id, type, declInfoOutParam));

			}
		}
		if (i < procOutParams.length) {
			typeError(impl, "Too few output parameters in " + impl);
		}

		processBody(impl.getBody(), impl.getIdentifier());

		mVarScopes.endScope();
		mTypeManager.popTypeScope();
	}

	/**
	 * Check if identifier id was already used in the definition of an in parameter, out parameter of local variable.
	 */
	private void checkIfAlreadyInOutLocal(final VarList vl, final String id) {
		if (mInParams.contains(id)) {
			typeError(vl, id + "already declared as in parameter");
		}
		if (mOutParams.contains(id)) {
			typeError(vl, id + "already declared as out parameter");
		}
		if (mLocalVars.contains(id)) {
			typeError(vl, id + "already declared as local variable");
		}
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			mDeclaredVars = new HashMap<>();
			mDeclaredFunctions = new HashMap<>();
			mDeclaredProcedures = new HashMap<>();
			mVarScopes = new ScopedHashMap<>();
			// pass1: parse type declarations
			mTypeManager = new TypeManager(unit.getDeclarations(),
					mServices.getLoggingService().getLogger(Activator.PLUGIN_ID));
			mTypeManager.init();
			// pass2: variable, constant and function declarations
			for (final Declaration decl : unit.getDeclarations()) {
				if (decl instanceof FunctionDeclaration) {
					processFunctionDeclaration((FunctionDeclaration) decl);
				} else if (decl instanceof VariableDeclaration) {
					processVariableDeclaration((VariableDeclaration) decl);
				} else if (decl instanceof ConstDeclaration) {
					processConstDeclaration((ConstDeclaration) decl);
				}
			}

			// pass2,5 :) LTL property declarations
			final LTLPropertyCheck propCheck = LTLPropertyCheck.getAnnotation(unit);
			if (propCheck != null) {
				for (final VariableDeclaration decl : propCheck.getGlobalDeclarations()) {
					processVariableDeclaration(decl);
				}
				for (final Entry<String, CheckableExpression> entry : propCheck.getCheckableAtomicPropositions()
						.entrySet()) {
					// FIXME: what about those statements?
					// for (Statement stmt : entry.getValue().getStatements()) {
					//
					// }
					typecheckExpression(entry.getValue().getExpression());
				}
			}

			// pass3: attributes function definition, axioms,
			// procedure declarations, where clauses
			for (final Declaration decl : unit.getDeclarations()) {
				typecheckAttributes(decl.getAttributes());
				if (decl instanceof ConstDeclaration) {
					checkConstDeclaration((ConstDeclaration) decl);
				} else if (decl instanceof FunctionDeclaration) {
					processFunctionDefinition((FunctionDeclaration) decl);
				} else if (decl instanceof Axiom) {
					typecheckExpression(((Axiom) decl).getFormula());
				} else if (decl instanceof Procedure) {
					processProcedureDeclaration((Procedure) decl);
				} else if (decl instanceof VariableDeclaration) {
					/* check where clauses */
					for (final VarList vl : ((VariableDeclaration) decl).getVariables()) {
						if (vl.getWhereClause() != null) {
							final BoogieType t = typecheckExpression(vl.getWhereClause());
							if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
								typeError(vl.getWhereClause(), "Where clause is not boolean: " + decl);
							}
						}
					}
				}
			}
			// pass4: procedure definitions, implementations
			for (final Declaration decl : unit.getDeclarations()) {
				if (decl instanceof Procedure) {
					processImplementation((Procedure) decl);
				}
			}
			return false;
		}
		return true;
	}

	private void typeError(final BoogieASTNode BoogieASTNode, final String message) {
		final TypeErrorResult<BoogieASTNode> result = new TypeErrorResult<>(BoogieASTNode, Activator.PLUGIN_ID,
				mServices.getBacktranslationService(), message);

		mServices.getLoggingService().getLogger(Activator.PLUGIN_ID)
				.error(BoogieASTNode.getLocation() + ": " + message);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		mServices.getProgressMonitorService().cancelToolchain();
	}

	private static void internalError(final String message) {
		throw new AssertionError(message);
	}

}
