//////////////////////////////////////////////////////////////////
//                         Demo of DD
//////////////////////////////////////////////////////////////////

package logic.add;

import graph.Graph;

import java.io.*;
import java.util.*;

public class Demo {

	public final static boolean USE_GRAPHVIZ_VIEWER = true;
	
	// General testing methods for the ADD class
	public static void main(String[] args) {
		Demo();
	}
	
	public static void Demo() {

		// Note: this only matters if you are using the automatic DD approximation method
		//       context.pruneNodes(...) demonstrated below.
		//
		//       The first argument to SetPruneInfo is the approximation type:
		//       - DD.REPLACE_MIN is a lower bound, 
		//       - DD.REPLACE_MAX is an upper bound, and
		//       - DD.REPLACE_AVG is the usual method that approximately minimizes deviation.
		//
		//       The second argument is the maximum error to introduce.
		FBR.SetPruneInfo(DD.REPLACE_AVG, 0.1d);

		// Here is where we create our variable ordering -- var IDs should be Integers >= 1
		// Here we're adding 10 variables {1,...,10}
		ArrayList order = new ArrayList();
	    for (int i = 1; i <= 10; i++) {
	    	order.add(new Integer(i));
	    }

	    // DD is the superclass of Table, ADD, AADD, etc.
	    DD context = new ADD(order); // new AADD(order); // new Table(order); 

	    // Let's create the function f = \sum_{i=1}^5 x_i
		int f = context.getConstantNode(0d); // gets constant
		for (int i = 1; i <= 5; i++) {
			int x_i = context.getVarNode(i, 0d, 1d); // gets indicator DD: (x_i ? 1d : 0d)
			f = context.applyInt(f, x_i, DD.ARITH_SUM);
		}
		
		// Let's look at it
		ViewDD(context, f);
		
		// int reduce_noise_dd = context.pruneNodes(noise_count_dd);
	}
	
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
