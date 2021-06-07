package cp;

import java.util.Arrays;
import java.util.Collections;
import java.util.Map;

import org.chocosolver.solver.Cause;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.nary.nvalue.amnv.differences.D;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.ESat;

import logic.add.DD;

/**
 * 
 * Propagator of an Affine Algebraic Decision Diagram constraint
 * 
 * 
 * @author giovannilobianco
 *
 */
public class DDPropagator extends Propagator<IntVar> {

	// -----------------------------------
	// -------- STATE VARIABLES ----------
	// -----------------------------------

	/**
	 * Decision Diagram representing the constraint
	 */
	public DD dd;

	/**
	 * ID of the root node of the DD
	 */
	public int rootID;

	/**
	 * isInstantiatedInDD[k]=true if the DD already considered that
	 * this.getVars()[k] is instantiated. Variables instantiated in the CP model
	 * are not necessarily instantiated in the DD. The whole purpose of this
	 * array is to detect variables whose instantiation have not been considered
	 * in the AADD yet.
	 */
	private boolean[] isInstantiatedInDD;

	/**
	 * Map each variable to their corresponding id in the DD
	 */
	public Map<IntVar, Integer> mapVarIndex;

	/**
	 * Record time spent in AADD algortihms
	 */
	public long timeAlgoDD = 0;

	/**
	 * Store node IDs for each x_i AADD
	 */
	public int[] xNode;

	/**
	 * Store node IDs for each (1-x_i) AADD
	 */
	public int[] oneMinusXNode;

	/**
	 * Store local index of variables. The index of x_i is i. However the local
	 * index of a variable depends on the propagator's variable instance:
	 * this.vars. If this.vars = [x_3, x_5, x_6, x_8] then local index of x_3 is
	 * 0, x_5 is 1, x_6 is 2 and x_8 is 3.
	 * 
	 */
	public int[] localIndex;

	// -------------------------------
	// -------- CONSTRUCTOR ----------
	// -------------------------------

	/**
	 * Constructor with the variables vars of the scope, decision diagram dd
	 * with its root node rootID and mapVarIndex linking each variable of vars
	 * with its corresponding id in dd.
	 * 
	 */
	public DDPropagator(IntVar[] vars, DD dd, int rootID, Map<IntVar, Integer> mapVarIndex) {
		super(vars);

		// Initializing DD
		this.dd = dd;
		this.rootID = rootID;
		dd.addSpecialNode(rootID); // special node can't be flushed from DD
									// cache. We want to prevent root IDs to be
									// flushed as we want to get back to
									// retrieve them when backtracking.
		this.mapVarIndex = mapVarIndex;

		// No variable is instantiated in the beginning
		this.isInstantiatedInDD = new boolean[vars.length];
		for (int k = 0; k < vars.length; k++) {
			this.isInstantiatedInDD[k] = false;
		}

		// Initializing localIndex
		int maxIndex = Collections.max(mapVarIndex.values());
		this.localIndex = new int[maxIndex + 1];
		Arrays.fill(localIndex, -1);

		// Building and storing x_i AADDs
		this.xNode = new int[vars.length];
		for (int i = 0; i < vars.length; i++) {
			xNode[i] = dd.getVarNode(mapVarIndex.get(vars[i]), 0d, 1d);
			dd.addSpecialNode(xNode[i]);
			localIndex[mapVarIndex.get(vars[i])] = i;
		}

		// Building and storing (1-x_i) AADDs
		this.oneMinusXNode = new int[vars.length];
		int one = dd.getConstantNode(1);
		for (int i = 0; i < vars.length; i++) {
			oneMinusXNode[i] = dd.applyInt(one, xNode[i], DD.ARITH_MINUS);
			dd.addSpecialNode(oneMinusXNode[i]);
		}
	}

	// ---------------------------
	// -------- GETTERS ----------
	// ---------------------------
	/**
	 * 
	 * @return local index of variable x
	 */
	public int getLocalIndexOf(IntVar x) {
		return localIndex[mapVarIndex.get(x)];
	}

	// ---------------------------
	// -------- METHODS ----------
	// ---------------------------

	@Override
	public void propagate(int evtmask) throws ContradictionException {

		// This condition can be met on first call of propagate() only, if the
		// input DD is inconsistent. For next calls of this method, the
		// propagator will necessarily not be entailed.
		// The Propagator may become not entailed during calls of acknowledge()
		// and modify(), but, if so, an exception is raised inside these
		// methods and this condition is never met here.
		if (this.isEntailed() == ESat.FALSE) {
			throw new ContradictionException();
		}

		// First acknowledge variables that have been instantiated since last
		// call of this method and then modify AADD accordingly, which may also
		// instantiate new variables in return.
		acknowledge();
		modify();
	}

	/**
	 * Look for variables that became instantiated since last call of
	 * propagate() and modify the DD accordingly: if a variable x has been
	 * instantiated to 0, we multiply the current DD by (1-x), if a variable x
	 * has been instantiated to 1, we multiply the current DD by x
	 * 
	 * @throws ContradictionException
	 */
	public void acknowledge() throws ContradictionException {

		for (int k = 0; k < vars.length; k++) {
			IntVar x = vars[k];
			if (x.isInstantiated() && !isInstantiatedInDD[k]) {
				int idxVar = getLocalIndexOf(x);

				// We store the rootID so we can backtrack to it later
				int rootSave = this.rootID;

				if (x.getValue() == 0) {
					// If x is instantiated to 0, we multiply the current DD by
					// (1-x)
					// We also store the time we spend in DD algorithms
					int one_minus_x = this.oneMinusXNode[idxVar];
					long start = System.currentTimeMillis();
					this.rootID = dd.applyInt(this.rootID, one_minus_x, DD.ARITH_PROD);
					this.timeAlgoDD += (System.currentTimeMillis() - start);
				} else {
					// If x is instantiated to 1, we multiply the current DD by
					// x
					int dd_x = this.xNode[idxVar];
					long start = System.currentTimeMillis();
					this.rootID = dd.applyInt(this.rootID, dd_x, DD.ARITH_PROD);
					this.timeAlgoDD += (System.currentTimeMillis() - start);
				}

				// Check if the new DD is consistent. If not, throws a
				// contradiction, which launches a backtrack procedure.
				if (dd.getMaxValue(this.rootID) == 0) {
					throw new ContradictionException();
				}

				isInstantiatedInDD[k] = true; // x's instantiation has now been
												// considered in the DD

				// Backtrack : x_k is not instantiated anymore and DD must be
				// set to previous state
				if (this.getModel().getEnvironment().getWorldIndex() > 1) {
					// We don't save modification of the initial propagation

					int k_save = k; // x local index to un-instantiate
					this.model.getEnvironment().save(() -> {
						isInstantiatedInDD[k_save] = false; // Un-instantiate x

						// We remove rootID from special node of the DD, and we
						// flush it, as it became useless since we need to
						// backtrack to a previous state of the DD.
						dd.removeSpecialNode(this.rootID);
						long start = System.currentTimeMillis();
						dd.flushCaches(false);
						this.timeAlgoDD += (System.currentTimeMillis() - start);

						// Get back to the previous state of the DD
						this.rootID = rootSave;
					});
				}

			}
		}
		dd.addSpecialNode(this.rootID); // We store the new rootID so we
		// can retrieve it later
	}

	/**
	 * Look for variables that are instantiated in the DD and modify the domains
	 * accordingly in the CP model. To test if a variable x's domain have been
	 * reduced to {0} (or {1}) in the DD, we multiply the DD by x (or by 1-x)
	 * and check if DD is still consistent or not. We do that test for each
	 * uninstantiated variable.
	 * 
	 * @throws ContradictionException
	 */
	public void modify() throws ContradictionException {
		for (int k = 0; k < vars.length; k++) {
			if (!isInstantiatedInDD[k]) {
				// Testing if x_k should be instantiated to 0
				IntVar x = vars[k];
				int idxVar = getLocalIndexOf(x);
				int dd_x = this.xNode[idxVar];

				long start = System.currentTimeMillis();
				// As this is only a test, we do not store the resulting AADD as
				// the new rootID
				int dd_prod_x = dd.applyInt(this.rootID, dd_x, DD.ARITH_PROD);
				this.timeAlgoDD += (System.currentTimeMillis() - start);

				// Test if dd_prod_x is not consistent
				if (dd.getMaxValue(dd_prod_x) == 0) {
					isInstantiatedInDD[k] = true;
					x.instantiateTo(0, Cause.Null);

					// Backtrack : x_k is not instantiated anymore
					if (this.getModel().getEnvironment().getWorldIndex() > 1) {
						// We don't save modification of the initial propagation
						int k_save = k;
						this.model.getEnvironment().save(() -> {
							// The AADD is not modified in this method, so we
							// just un-instantiate x when backtracking.
							isInstantiatedInDD[k_save] = false;
						});
					}

				} else {
					// Idem for testing if x_k should be instantiated to 1
					int one_minus_x = this.oneMinusXNode[idxVar];

					start = System.currentTimeMillis();
					int dd_prod_one_minus_x = dd.applyInt(this.rootID, one_minus_x, DD.ARITH_PROD);
					this.timeAlgoDD += (System.currentTimeMillis() - start);

					if (dd.getMaxValue(dd_prod_one_minus_x) == 0) {
						isInstantiatedInDD[k] = true;
						x.instantiateTo(1, Cause.Null);

						// Backtrack : x_k is not instantiated anymore
						if (this.getModel().getEnvironment().getWorldIndex() > 1) {
							// We don't save modification of the initial
							// propagation
							int k_save = k;
							this.model.getEnvironment().save(() -> {
								isInstantiatedInDD[k_save] = false;
							});
						}
					}
				}

			}
		}
		// We flush all the dd tests we have build.
		long start = System.currentTimeMillis();
		dd.flushCaches(false);
		this.timeAlgoDD += (System.currentTimeMillis() - start);
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
