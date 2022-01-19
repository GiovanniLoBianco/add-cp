package cp;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import org.chocosolver.solver.Cause;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.ESat;

import logic.add.ADD;
import logic.add.ADDINode;
import logic.add.DD;
import logic.add.Demo;

public class ADDPropagator extends Propagator<IntVar> {

	// -----------------------------------
	// -------- STATE VARIABLES ----------
	// -----------------------------------

	/**
	 * Decision Diagram representing the constraint
	 */
	public ADD dd;

	/**
	 * ID of the root node of the DD
	 */
	public int rootID;

	/**
	 * Map each variable to their corresponding id in the DD
	 */
	public Map<IntVar, Integer> mapVarIndex;

	/**
	 * Map each variable's index to their corresponding variable
	 */
	public Map<Integer, IntVar> mapIndexVar;

	/**
	 * Map each variable global index to local index
	 */
	public Map<Integer, Integer> mapGlobalLocalIndex;

	// -------------------------------
	// -------- CONSTRUCTOR ----------
	// -------------------------------

	/**
	 * 
	 * @param vars        array of variables involved in the constraint. MUST BE SORTED IN THE SAME ORDER AS IN THE ADD.
	 * @param dd          ADD representing the constraint
	 * @param rootID      node id of the root of dd
	 * @param mapVarIndex map every variable of vars to a single index
	 */
	public ADDPropagator(IntVar[] vars, ADD dd, int rootID, Map<IntVar, Integer> mapVarIndex) {
		super(vars);
		this.dd = dd;
		this.rootID = rootID;
		dd.addSpecialNode(rootID);
		this.mapVarIndex = mapVarIndex;

		this.mapIndexVar = new HashMap<Integer, IntVar>();
		for (IntVar var : vars) {
			mapIndexVar.put(mapVarIndex.get(var), var);
		}

		this.mapGlobalLocalIndex = new HashMap<Integer, Integer>();
		for (int i = 0; i < vars.length; i++) {
			mapGlobalLocalIndex.put(mapVarIndex.get(vars[i]), i);
		}

	}

	@Override
	public void propagate(int evtmask) throws ContradictionException {
		// TODO Auto-generated method stub

		if (isEntailed() == ESat.FALSE) {
			throw new ContradictionException();
		}

		int rootIDsave = rootID;

		// Backtrack procedure
		this.model.getEnvironment().save(() -> {
			dd.removeSpecialNode(this.rootID);
			//dd.flushCaches(false);
			this.rootID = rootIDsave;
		});

		boolean[] visitedVars = new boolean[vars.length];
		Arrays.fill(visitedVars, false);

		// Detect values that become inconsistent in the ADD if we propagate new
		// instantiated variables
		boolean[][] inconsistentValues = detectInconsistentValues(visitedVars);

		// Update ADD by propagating new instantiated variables
		for (int i = 0; i < vars.length; i++) {
			if (visitedVars[i] && vars[i].isInstantiated()) {
				int b = vars[i].getValue();
				int varID = mapVarIndex.get(vars[i]);
				if (b == 0) {
					rootID = dd.restrict(rootID, varID, DD.RESTRICT_LOW);
				} else {
					rootID = dd.restrict(rootID, varID, DD.RESTRICT_HIGH);
				}
				if (isEntailed() == ESat.FALSE) {
					throw new ContradictionException();
				}

			}
		}

		// Update domains of variables
		for (int i = 0; i < vars.length; i++) {
			if (visitedVars[i]) {
				for (int b = 0; b <= 1; b++) {
					if (!inconsistentValues[i][b]) {
						vars[i].removeValue(b, Cause.Null);
					}
				}
			}
		}

		dd.addSpecialNode(this.rootID);

	}

	/**
	 * 
	 * @return array of boolean such that r_assign[i][b] == true iff x_i has not
	 *         been instantiated before AND b is a consistent value in domain of i.
	 */
	public boolean[][] detectInconsistentValues(boolean[] visitedVars) {

		boolean[] visited = new boolean[rootID + 1];
		Arrays.fill(visited, false);
		boolean[][] r_assign = new boolean[vars.length][2];
		for (int i = 0; i < vars.length; i++) {
			r_assign[i][0] = false;
			r_assign[i][1] = false;
		}
		boolean[] r_node = new boolean[rootID + 1];
		Arrays.fill(r_node, false);

		DFS(rootID, r_assign, r_node, visited, visitedVars);

		return r_assign;
	}

	/**
	 * 
	 * @param id       ID of the node visited
	 * @param r_assign array of possible assignment. r_assign[k][b]==true iff b is a
	 *                 consistent value of vars[k], considering the states of other
	 *                 variables
	 * @param r_node   r_node[id]==true iff it is possible to reach state "1" from
	 *                 node id
	 * @param visited  array of already visited nodes
	 * @return true if state "1" can be reached from node id
	 */
	public boolean DFS(int id, boolean[][] r_assign, boolean[] r_node, boolean[] visited, boolean[] visitedVars) {

		// Base case: state 0, state 1 or already visited
		if (dd.getMaxValue(id) == 0) {
			return false;
		} else if (dd.getMinValue(id) == 1) {
			return true;
		} else if (visited[id]) {
			return r_node[id];
		} else {
			ADDINode node = (ADDINode) dd.getNode(id);
			IntVar var = mapIndexVar.get(node._nGlobalID);
			visitedVars[mapGlobalLocalIndex.get(node._nGlobalID)] = true;

			// Case: node correspond to a new instantiated variable and only one child node
			// must be visited
			if (var.isInstantiated()) {
				int b = 0; // value assigned to var
				int idChild = node._nLow;
				if (var.getValue() == 1) {
					b = 1;
					idChild = node._nHigh;
				}
				r_node[id] = DFS(idChild, r_assign, r_node, visited, visitedVars);
				r_assign[mapGlobalLocalIndex.get(node._nGlobalID)][b] |= r_node[id];

				// Children nodes can skip many variables decision
				int beginSkip = mapGlobalLocalIndex.get(node._nGlobalID) + 1;
				int endSkip = -1;
				if (dd.getMaxValue(idChild) == 0 || dd.getMinValue(idChild) == 1) {
					endSkip = vars.length;
				} else {
					ADDINode nodeChild = (ADDINode) dd.getNode(idChild);
					endSkip = mapGlobalLocalIndex.get(nodeChild._nGlobalID);
				}

				for (int k = beginSkip; k < endSkip; k++) {
					r_assign[k][0] |= r_node[id];
					r_assign[k][1] |= r_node[id];
				}

			} else {
				// Case: node correspond to an uninstantiated variable and both children nodes
				// must be visited
				boolean r_l = DFS(node._nLow, r_assign, r_node, visited, visitedVars);
				boolean r_h = DFS(node._nHigh, r_assign, r_node, visited, visitedVars);
				r_node[id] = r_l || r_h;
				r_assign[mapGlobalLocalIndex.get(node._nGlobalID)][0] |= r_l;
				r_assign[mapGlobalLocalIndex.get(node._nGlobalID)][1] |= r_h;

				// Children nodes can skip many variables decision...
				int beginSkip = mapGlobalLocalIndex.get(node._nGlobalID) + 1;

				// ... on low child node
				int endSkip_low = -1;
				if (dd.getMaxValue(node._nLow) == 0 || dd.getMinValue(node._nLow) == 1) {
					endSkip_low = vars.length;
				} else {
					ADDINode node_low = (ADDINode) dd.getNode(node._nLow);
					endSkip_low = mapGlobalLocalIndex.get(node_low._nGlobalID);
				}
				for (int k = beginSkip; k < endSkip_low; k++) {
					r_assign[k][0] |= r_l;
					r_assign[k][1] |= r_l;
				}

				// ... on high child node
				int endSkip_high = -1;
				if (dd.getMaxValue(node._nHigh) == 0 || dd.getMinValue(node._nHigh) == 1) {
					endSkip_high = vars.length;
				} else {
					ADDINode node_high = (ADDINode) dd.getNode(node._nHigh);
					endSkip_high = mapGlobalLocalIndex.get(node_high._nGlobalID);
				}
				for (int k = beginSkip; k < endSkip_high; k++) {
					r_assign[k][0] |= r_h;
					r_assign[k][1] |= r_h;
				}
			}

			visited[id] = true;
			return r_node[id];
		}
	}

	// If the min value of the DD is 1 then, every path leads to 1 and then the
	// constraint is entailed. Vice-versa if max value is 0. Otherwise we cannot
	// determine.
	@Override
	public ESat isEntailed() {
		// TODO Auto-generated method stub
		if (dd.getMinValue(rootID) == 1) {
			return ESat.TRUE;
		}
		if (dd.getMaxValue(rootID) == 0) {
			return ESat.FALSE;
		}
		return ESat.UNDEFINED;
	}

}
