/* ForkStatement -- Automatically generated by TreeBuilder */

package de.uni_freiburg.informatik.ultimate.boogie.ast;

import java.util.List;
import java.util.Arrays;
import java.util.ArrayList;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import java.util.Arrays;
/**
 * A asynchrone procedure call.
 * The arguments are evaluated before the procedure call and then
 * the side-effects of the procedure call occur.
 */
public class ForkStatement extends Statement {
    private static final long serialVersionUID = 1L;
    private static final java.util.function.Predicate<BoogieASTNode> VALIDATOR = 
			BoogieASTNode.VALIDATORS.get(ForkStatement.class);
    /**
     * An id referencing that fork statement out of multiple ones.
     */
    Expression forkID;

    /**
     * The name of the procedure.
     */
    String methodName;

    /**
     * The arguments. This must contain the same number of expressions
     * as there are input parameters to the procedure.
     * If {@link #isForall()} is true, the argument can be a wildcard
     * and the procedure is &ldquo;called&rdquo; for all possible values.
     * This is used for lemma procedures which should not have any
     * side effects.
     */
    Expression[] arguments;

    /**
     * The constructor taking initial values.
     * @param loc the location of this node
     * @param forkID an id referencing that fork statement out of multiple ones.
     * @param methodName the name of the procedure.
     * @param arguments the arguments.
     */
    public ForkStatement(ILocation loc, Expression forkID, String methodName, Expression[] arguments) {
        super(loc);
        this.forkID = forkID;
        this.methodName = methodName;
        this.arguments = arguments;
        assert VALIDATOR == null || VALIDATOR.test(this) : "Invalid ForkStatement: " + this;
    }

    /**
     * Returns a textual description of this object.
     */
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append("ForkStatement").append('[');
        sb.append(forkID);
        sb.append(',').append(methodName);
        sb.append(',');
        if (arguments == null) {
            sb.append("null");
        } else {
            sb.append('[');
            for(int i1 = 0; i1 < arguments.length; i1++) {
                if (i1 > 0) sb.append(',');
                    sb.append(arguments[i1]);
            }
            sb.append(']');
        }
        return sb.append(']').toString();
    }

    /**
     * Gets an id referencing that fork statement out of multiple ones.
     * @return an id referencing that fork statement out of multiple ones.
     */
    public Expression getForkID() {
        return forkID;
    }

    /**
     * Gets the name of the procedure.
     * @return the name of the procedure.
     */
    public String getMethodName() {
        return methodName;
    }

    /**
     * Gets the arguments. This must contain the same number of expressions
     * as there are input parameters to the procedure.
     * If {@link #isForall()} is true, the argument can be a wildcard
     * and the procedure is &ldquo;called&rdquo; for all possible values.
     * This is used for lemma procedures which should not have any
     * side effects.
     * @return the arguments.
     */
    public Expression[] getArguments() {
        return arguments;
    }

    public List<BoogieASTNode> getOutgoingNodes() {
        List<BoogieASTNode> children = super.getOutgoingNodes();
        children.add(forkID);
        if(arguments!=null){
            children.addAll(Arrays.asList(arguments));
        }
        return children;
    }

    public void accept(GeneratedBoogieAstVisitor visitor) {
        if(visitor.visit((Statement)this)){
                } else {
                        return;
                        }
        if(visitor.visit(this)){
            if(forkID!=null){
                forkID.accept(visitor);
            }
            if(arguments!=null){
                for(Expression elem : arguments){
                    elem.accept(visitor);
                }
            }
        }
    }

    public ForkStatement accept(GeneratedBoogieAstTransformer visitor) {
        ForkStatement node = visitor.transform(this);
        if(node != this){
            return node;
        }

            Expression newforkID = null;
        if(forkID != null){
            newforkID = forkID.accept(visitor);
        }
        boolean isChanged=false;
            ArrayList<Expression> tmpListnewarguments = new ArrayList<>();
        if(arguments != null){
            for(Expression elem : arguments){
                Expression newarguments = elem.accept(visitor);
                isChanged = isChanged || newarguments != elem;
                tmpListnewarguments.add(elem.accept(visitor));
            }
        }
        if(isChanged || forkID != newforkID){
            return new ForkStatement(loc, newforkID, methodName, tmpListnewarguments.toArray(new Expression[0]));
        }
        return this;
    }
}
