//////////////////////////////////////////////////////////////////
//                         Demo of DD
//////////////////////////////////////////////////////////////////

package logic.add;

import graph.Graph;

import java.io.*;
import java.util.*;

public class Demo {

	// Change this to false if the Graphviz 2.28 has not been installed
	public final static boolean USE_GRAPHVIZ_VIEWER = true;
	
	public static void main(String[] args) {
		Demo();
	}
	
	public static void Demo() {

		// Here is where we create our variable ordering -- var IDs should be Integers >= 1
		// Here we're adding 10 variables {1,...,10}
		ArrayList order = new ArrayList();
	    for (int i = 1; i <= 10; i++) {
	    	order.add(new Integer(i));
	    }

	    // DD is the superclass of Table, ADD, AADD -- so just instantiate the subclass you want
	    //DD context = new Table(order);
	    DD context = new ADD(order);
	    //DD context = new AADD(order);
	    	
	    // Let's create the function f = \sum_{i=1}^5 x_i
		int f = context.getConstantNode(0d); // gets constant
		for (int i = 1; i <= 5; i++) {
			int x_i = context.getVarNode(i, 0d, 1d); // gets indicator DD: (x_i ? 1d : 0d)
			f = context.applyInt(f, x_i, DD.ARITH_SUM);
		}
		
		// Let's look at it
		ViewDD(context, f);
		
		// Now let's create g = I[f >= 3] and look at it
		int g = context.applyInt(f, context.getConstantNode(3d), DD.COMP_GREATEQ);
		ViewDD(context, g);
		
		// Finally, let's approximate the DD... first we specify how to approximate:
		// * The first argument to SetPruneInfo is the approximation type, i.e.,
		//   - DD.REPLACE_MIN is a lower bound, 
		//   - DD.REPLACE_MAX is an upper bound, and
		//   - DD.REPLACE_AVG is the usual method that approximately minimizes deviation.
		// * The second argument to SetPruneInfo is the maximum error to introduce.
		FBR.SetPruneInfo(DD.REPLACE_MIN, 2d);
		
		// Now let's find a smaller DD that is a strict lower bound and has max error 1d
		int lb = context.pruneNodes(f);
		ViewDD(context, lb);
		
		// And let's do the same, but an upper bound instead
		FBR.SetPruneInfo(DD.REPLACE_MAX, 2d);
		int ub = context.pruneNodes(f);
		ViewDD(context, ub);
		
		// Finally, let's look at the over-restricted and over-relaxed constraints we can get
		// ... note that when we compute g = I[lb >= 3], g is an over-restricted constraint 
		//     (it says false in some cases where it should say true)
		int g_over_restricted = context.applyInt(lb, context.getConstantNode(3d), DD.COMP_GREATEQ);
		ViewDD(context, g_over_restricted);

		// ... note that when we compute g = I[ub >= 3], g is an over-relaxed constraint 
		//     (it says true in some cases where it should say false)
		int g_over_relaxed = context.applyInt(ub, context.getConstantNode(3d), DD.COMP_GREATEQ);
		ViewDD(context, g_over_relaxed);

	}
	
	/** Helper function for viewing DDs either with GraphViz or to text console **/
	public static void ViewDD(DD context, int f) {
		if (USE_GRAPHVIZ_VIEWER) {
		    // Build the DAG Graph for the DD and launch the Java viewer
			// Note: can also use command line methods to view generated dot file below
			Graph g = context.getGraph(f);
			g.genDotFile("temp_dd.dot");
			g.launchViewer(1300, 770);
		} else { 
			// Print to screen
			System.out.println("Node ID " + f + " [" + context.countExactNodes(f) + "]:\n" + context.printNode(f) + "\n");
			
			// Optionally print out the tabular view of the function (only works if few variables)
			//DD.PrintEnum(context,f);
		}
	}
}
