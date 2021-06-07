package cp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;

import org.chocosolver.solver.Cause;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.search.strategy.Search;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.ESat;

import logic.add.AADD;
import logic.add.DD;
import logic.add.Demo;

/**
 * 
 * This Class is a tool class for running experiments to test DDPropagator
 *
 * @author giovannilobianco
 *
 */
public class DDPropagatorXP {

	// ------------------------------------------------------------
	// ------------------ PROBLEMS GENERATION----------------------
	// ------------------------------------------------------------

	/**
	 * <pre>
	 * Add integer variables into the CP Model as their boolean variables
	 * decomposition.
	 * 
	 * If domains[i] = [1,5] then we create 3 boolean variables such that
	 * x_i= 1 + b_0 + 2b_1 + 4b_2. 
	 * 
	 * Then we must constrain b_0, b_1 and b_2 to make sure x_i takes its value only in domain[i]. 
	 * These constraints are expressed as decision diagrams, for each variable.
	 * 
	 * If all domains are in the format [0, 2^k-1], then there is no need to create a constraint for each domain.
	 * 
	 * We store all the boolean variables into a hashmap, so that we can use other
	 * AADD constraints over the same set of variables.
	 * </pre>
	 * 
	 * 
	 * @param model
	 * @param domains
	 *            domains[i] is the integer domain of variable i
	 * @param mapVarIndex_Expr
	 *            Hashmap of every new boolean variables with their
	 *            corresponding index. Will be used when creating expression
	 *            based on these boolean variables.
	 * @param areDomainConstrained
	 *            false if domains are in this format [0, 2^k-1], true otherwise
	 * 
	 * @return Array of lists of required boolean variable indices for each
	 *         integer variable.
	 */
	public static ArrayList<Integer>[] addIntegerVariablesDD(Model model, int[][] domains,
			HashMap<IntVar, Integer> mapVarIndex_Expr, boolean areDomainsConstrained) {

		// number of variables
		int n = domains.length;

		// Map between binary variables and their indices, for each domain
		HashMap<IntVar, Integer>[] mapVarIndex_Domains = new HashMap[n];

		// For each integer variable, we store the required boolean variables'
		// indices
		ArrayList<Integer>[] idxBooleanVarLists = new ArrayList[n];

		int idxBooleanVar = 0;
		for (int i = 0; i < n; i++) {
			// Compute the number of required boolean variables
			int min = domains[i][0];
			int max = domains[i][domains[i].length - 1];
			int nbBooleanVars = (int) Math.floor(Math.log(max - min) / Math.log(2) + 1);

			// Create the boolean variables and store them in DDs' maps
			idxBooleanVarLists[i] = new ArrayList<Integer>();
			mapVarIndex_Domains[i] = new HashMap<IntVar, Integer>();
			for (int k = 0; k < nbBooleanVars; k++) {
				BoolVar b_k = model.boolVar("b_" + idxBooleanVar);
				mapVarIndex_Domains[i].put(b_k, idxBooleanVar);
				mapVarIndex_Expr.put(b_k, idxBooleanVar);
				idxBooleanVarLists[i].add(idxBooleanVar);
				idxBooleanVar++;
			}

			if (areDomainsConstrained) {
				// Create AADD representing x_i as its boolean sum
				// decompositions
				DD domain_i = new AADD(idxBooleanVarLists[i]);
				int x_i = domain_i.getConstantNode(min);
				for (int k = 0; k < nbBooleanVars; k++) {
					int b_k = domain_i.getVarNode(idxBooleanVarLists[i].get(k), 0d, 1d);
					int two_pw_k = domain_i.getConstantNode(Math.pow(2, k));
					int term_k = domain_i.applyInt(two_pw_k, b_k, DD.ARITH_PROD);
					x_i = domain_i.applyInt(x_i, term_k, DD.ARITH_SUM);
				}
				int maxBound = domain_i.getConstantNode(max);
				int bounded_x_i = domain_i.applyInt(x_i, maxBound, DD.COMP_LESSEQ);

				// Create AADD constraint, binding variables of the model to
				// AADD
				// structure
				Set<IntVar> boolVarSet = mapVarIndex_Domains[i].keySet();
				IntVar[] booleanVars_i = new IntVar[boolVarSet.size()];
				booleanVars_i = boolVarSet.toArray(booleanVars_i);
				Constraint cstr_domain_i = new Constraint("Domain_" + i,
						new DDPropagator(booleanVars_i, domain_i, bounded_x_i, mapVarIndex_Domains[i]));
				cstr_domain_i.post();
			}
		}

		return idxBooleanVarLists;

	}

	/**
	 * <pre>
	 * Generate randomized domains for n variables.
	 * Each domain's lower and upper bound are randomized by taking a random value uniformly in [l,u].
	 * </pre>
	 * 
	 */
	public static int[][] generateRandomDomains(Model model, int n, int l, int u, Random rnd) {

		int[][] domains = new int[n][2];
		for (int i = 0; i < n; i++) {
			int a = rnd.nextInt(u + 1 - l) + l;
			int b = rnd.nextInt(u + 1 - l) + l;
			if (a == b) {
				b++;
			}
			domains[i][0] = Math.min(a, b);
			domains[i][1] = Math.max(a, b);
		}
		return domains;
	}

	/**
	 * Generate randomized domains for n variables. Each varaibles have a domain
	 * [0, 2^k-1] with k randomly and uniformly chosen in [k_min, k_max]
	 */
	public static int[][] generateRandom2kDomains(Model model, int n, int k_min, int k_max, Random rnd) {
		int[][] domains = new int[n][2];
		for (int i = 0; i < n; i++) {
			int k = rnd.nextInt(k_max - k_min + 1) + k_min;
			int u = (int) (Math.pow(2, k) - 1);
			domains[i][0] = 0;
			domains[i][1] = u;
		}
		return domains;
	}

	/**
	 * <pre>
	 * Create a sum expression as a decision diagram using integer variables
	 * whose indices are in usedVars and coefficientss given by coeffs.
	 * 
	 * Also add used boolena variables inside a set that will be used for creating the constraint.
	 * 
	 * </pre>
	 * 
	 * @param usedVars
	 *            gives the integer variables used in the sum expression.
	 * @param dd
	 *            decision diagram in which we create the sum expression.
	 * @param coeffs
	 *            coefficients for each used variables in the sum expression.
	 *            Must be same size as usedVars.
	 * @param domains
	 *            gives the interval domain of each integer variable.
	 * @param idxBooleanVarLists
	 *            gives the indices of the boolean variables required to
	 *            represent each integer variable.
	 * @param boolVarArray
	 *            array of all boolean variables in the model in order of
	 *            insertion
	 * @param boolVarSet
	 *            set of boolean variables that are used in the constraint.
	 * 
	 */
	public static int generateSumDD(DD dd, int[] usedVars, int[] coeffs, int[][] domains,
			ArrayList<Integer>[] idxBooleanVarLists, IntVar[] boolVarArray, HashSet<IntVar> boolVarSet) {

		int l = usedVars.length;

		int sum = dd.getConstantNode(0);
		for (int i = 0; i < l; i++) {
			int idxVar_l = usedVars[i];

			int x_i = dd.getConstantNode(domains[idxVar_l][0]);
			for (int k = 0; k < idxBooleanVarLists[idxVar_l].size(); k++) {
				int two_pw_k = dd.getConstantNode(Math.pow(2, k));
				int b_k = dd.getVarNode(idxBooleanVarLists[idxVar_l].get(k), 0d, 1d);
				boolVarSet.add(boolVarArray[idxBooleanVarLists[idxVar_l].get(k)]);
				int term_k = dd.applyInt(two_pw_k, b_k, DD.ARITH_PROD);
				x_i = dd.applyInt(x_i, term_k, DD.ARITH_SUM);
			}

			int coeff_i = dd.getConstantNode(coeffs[i]);
			int term_i = dd.applyInt(coeff_i, x_i, DD.ARITH_PROD);

			sum = dd.applyInt(sum, term_i, DD.ARITH_SUM);

		}
		return sum;

	}

	/**
	 * <pre>
	 * Select randomly m variables among n integer variables.
	 * Choose uniformly randomly a coefficient for each selected variable in [l,u]
	 * </pre>
	 * 
	 * 
	 * @param n
	 *            number of variables in total
	 * @param m
	 *            number of variables in the expression
	 * @param l
	 *            lower bound for coefficients
	 * @param u
	 *            upper bound for coefficients
	 * @param rnd
	 * @return array of selected variables indices and array of coefficients
	 */
	public static int[][] generateRandomTerms(int n, int m, int l, int u, Random rnd) {

		// Select randomly m variables among n variables
		ArrayList<Integer> listVariables = new ArrayList<Integer>();
		for (int i = 0; i < n; i++) {
			listVariables.add(i);
		}
		Collections.shuffle(listVariables, rnd);
		while (listVariables.size() > m) {
			listVariables.remove(m);
		}
		Collections.sort(listVariables);

		// Select random coefficients
		int[] coeffs = new int[m];
		for (int i = 0; i < m; i++) {
			do {
				coeffs[i] = rnd.nextInt(u - l + 1) + l;
			} while (coeffs[i] == 0);
		}

		// We store variables indices and their coeff in the same structure
		int[][] randomTerms = new int[2][m];
		for (int i = 0; i < m; i++) {
			randomTerms[0][i] = listVariables.get(i);
		}
		randomTerms[1] = coeffs;

		return randomTerms;

	}

	/**
	 * 
	 * Create a random model with nc random linear constraints One model using
	 * DD propagators and one model using expression trees.
	 * 
	 * @param n
	 *            number of variables
	 * @param nc
	 *            number of constraints
	 * @param m
	 *            number of variables in each expression
	 * @param l_dom
	 *            lower bound for domains' generation
	 * @param u_dom
	 *            upper bound for domains' generation
	 * @param l_coeff
	 *            lower bound for coefficients' generation
	 * @param u_coeff
	 *            upper bound for coefficients' generation
	 * @param diff
	 *            adjust the difficulty of satisfy each constraint, it defines
	 *            the constant in expression <= bound. bound =
	 *            range_min+(1-diff)*(range_max-range_min) where range is the
	 *            range of the expression.
	 * @param domain2k
	 *            true iff domains' format are [0, 2^k-1], then k is randomly
	 *            chosen between l_dom and u_dom
	 * @param seed
	 * @return a CP Model
	 */
	public static Model[] generateRandomLinearModel(int n, int nc, int m, int l_dom, int u_dom, int l_coeff,
			int u_coeff, double diff, boolean domain2k, long seed) {

		// Init
		Random rnd = new Random(seed);
		Model model = new Model("Random Linear Constraints with Decision Diagrams");
		Model model_tree = new Model("Random Linear Constraints with Expression Tree");

		// Generate random domains and insert variables in the model
		int[][] domains;
		if (domain2k) {
			domains = generateRandom2kDomains(model, n, l_dom, u_dom, rnd);
		} else {
			domains = generateRandomDomains(model, n, l_dom, u_dom, rnd);
		}
		HashMap<IntVar, Integer> mapBoolVarIndex = new HashMap<IntVar, Integer>();
		ArrayList<Integer>[] idxBooleanVarLists = addIntegerVariablesDD(model, domains, mapBoolVarIndex, !domain2k);

		// Create integer variables in model_tree
		IntVar[] vars_tree = new IntVar[n];
		for (int i = 0; i < n; i++) {
			vars_tree[i] = model_tree.intVar("x_" + i, domains[i][0], domains[i][1]);
		}

		// Create Random Linear Constraints
		ArrayList<Integer> ordering = new ArrayList<Integer>();
		ordering.addAll(mapBoolVarIndex.values());
		for (int j = 0; j < nc; j++) {
			// Init DD
			DD dd = new AADD(ordering);

			// Gather all boolean variables used in the constraint
			HashSet<IntVar> boolVarSet = new HashSet<IntVar>();

			// Creation of random expression with m random variables
			int[][] randomTerms = generateRandomTerms(n, m, l_coeff, u_coeff, rnd);
			int expr = generateSumDD(dd, randomTerms[0], randomTerms[1], domains, idxBooleanVarLists,
					model.retrieveIntVars(true), boolVarSet);

			// Compute bound
			int max = (int) Math.floor(dd.getMaxValue(expr));
			int min = (int) Math.ceil(dd.getMinValue(expr));
			int bound = (int) Math.round(min + (1 - diff) * (max - min));

			// Create arithm constraint
			int boundNodeDD = dd.getConstantNode(bound);
			int ineq = dd.applyInt(expr, boundNodeDD, DD.COMP_LESSEQ);
			IntVar[] usedBoolVars = new IntVar[boolVarSet.size()];
			usedBoolVars = boolVarSet.toArray(usedBoolVars);
			Constraint arithm = new Constraint("c_" + j, new DDPropagator(usedBoolVars, dd, ineq, mapBoolVarIndex));
			arithm.post();

			// Add constraints to model_tree
			int[] coeffs_tree = new int[n];
			Arrays.fill(coeffs_tree, 0);
			for (int l = 0; l < m; l++) {
				coeffs_tree[randomTerms[0][l]] = randomTerms[1][l];
			}
			model_tree.scalar(vars_tree, coeffs_tree, "<=", bound).post();

		}

		Model[] models = new Model[2];
		models[0] = model;
		models[1] = model_tree;

		return models;

	}

	/**
	 * 
	 * Create two random models with nc random quadratic constraints. One model
	 * using DD propagators and one model using expression trees.
	 * 
	 * @param n
	 *            number of variables
	 * @param nc
	 *            number of constraints
	 * @param l_dom
	 *            lower bound for domains' generation
	 * @param u_dom
	 *            upper bound for domains' generation
	 * @param l_coeff
	 *            lower bound for coefficients' generation
	 * @param u_coeff
	 *            upper bound for coefficients' generatio
	 * @param diff
	 *            adjust the difficulty of satisfy each constraint, it defines
	 *            the constant in expression <= cste. cste =
	 *            range_min+(1-diff)*(range_max-range_min) where range is the
	 *            range of the expression.
	 * @param domain2k
	 *            true iff domains' format are [0, 2^k-1], then k is randomly
	 *            chosen between l_dom and u_dom
	 * @param seed
	 * @return a CP Model
	 */
	public static Model[] generateRandomQuadraticModel(int n, int nc, int m, int l_dom, int u_dom, int l_coeff,
			int u_coeff, double diff, boolean domain2k, long seed) {

		// Init
		Random rnd = new Random(seed);
		Model model = new Model("Random Quadratic Constraints with Decision Diagrams");
		Model model_tree = new Model("Random Linear Constraints with Expression Tree");

		// Generate random domains and insert variables in the model
		int[][] domains;
		if (domain2k) {
			domains = generateRandom2kDomains(model, n, l_dom, u_dom, rnd);
		} else {
			domains = generateRandomDomains(model, n, l_dom, u_dom, rnd);
		}
		HashMap<IntVar, Integer> mapBoolVarIndex = new HashMap<IntVar, Integer>();
		ArrayList<Integer>[] idxBooleanVarLists = addIntegerVariablesDD(model, domains, mapBoolVarIndex, !domain2k);

		// Create integer variables in model_tree
		IntVar[] vars_tree = new IntVar[n];
		for (int i = 0; i < n; i++) {
			vars_tree[i] = model_tree.intVar("x_" + i, domains[i][0], domains[i][1]);
		}

		// Create Random Quadratic Constraints
		ArrayList<Integer> ordering = new ArrayList<Integer>();
		ordering.addAll(mapBoolVarIndex.values());
		for (int j = 0; j < nc; j++) {
			// Init DD
			DD dd = new AADD(ordering);

			// Gather all boolean variables used in the constraint
			HashSet<IntVar> boolVarSet = new HashSet<IntVar>();

			// Creation two random expression with a random number of variables
			int[][] randomTerms1 = generateRandomTerms(n, m, l_coeff, u_coeff, rnd);
			int expr1 = generateSumDD(dd, randomTerms1[0], randomTerms1[1], domains, idxBooleanVarLists,
					model.retrieveIntVars(true), boolVarSet);

			int[][] randomTerms2 = generateRandomTerms(n, m, l_coeff, u_coeff, rnd);
			int expr2 = generateSumDD(dd, randomTerms2[0], randomTerms2[1], domains, idxBooleanVarLists,
					model.retrieveIntVars(true), boolVarSet);

			// Multiply both expression
			int expr = dd.applyInt(expr1, expr2, DD.ARITH_PROD);

			// Compute bound
			int max = (int) Math.floor(dd.getMaxValue(expr));
			int min = (int) Math.ceil(dd.getMinValue(expr));
			int bound = (int) Math.round(min + (1 - diff) * (max - min));

			// Create arithm constraint
			int ineq = dd.applyInt(expr, dd.getConstantNode(bound), DD.COMP_LESSEQ);
			IntVar[] usedBoolVars = new IntVar[boolVarSet.size()];
			usedBoolVars = boolVarSet.toArray(usedBoolVars);
			Constraint quad = new Constraint("c_" + j, new DDPropagator(usedBoolVars, dd, ineq, mapBoolVarIndex));
			quad.post();

			// Add constraints to model_tree
			int[] coeffs1_tree = new int[n];
			Arrays.fill(coeffs1_tree, 0);
			for (int l = 0; l < m; l++) {
				coeffs1_tree[randomTerms1[0][l]] = randomTerms1[1][l];
			}
			IntVar expr1_tree = model_tree.intVar("expr1", (int) Math.ceil(dd.getMinValue(expr1)),
					(int) Math.floor(dd.getMaxValue(expr1)));
			model_tree.scalar(vars_tree, coeffs1_tree, "=", expr1_tree).post();

			int[] coeffs2_tree = new int[n];
			Arrays.fill(coeffs2_tree, 0);
			for (int l = 0; l < m; l++) {
				coeffs2_tree[randomTerms2[0][l]] = randomTerms2[1][l];
			}
			IntVar expr2_tree = model_tree.intVar("expr2", (int) Math.ceil(dd.getMinValue(expr2)),
					(int) Math.floor(dd.getMaxValue(expr2)));
			model_tree.scalar(vars_tree, coeffs2_tree, "=", expr2_tree).post();

			IntVar expr_tree = model_tree.intVar("expr", min, bound);
			model_tree.times(expr1_tree, expr2_tree, expr_tree).post();

		}

		Model[] models = new Model[2];
		models[0] = model;
		models[1] = model_tree;

		return models;

	}

	/**
	 * 
	 * Create two random models with nc random cubic constraints. One model
	 * using DD propagators and one model using expression trees.
	 * 
	 * @param n
	 *            number of variables
	 * @param nc
	 *            number of constraints
	 * @param l_dom
	 *            lower bound for domains' generation
	 * @param u_dom
	 *            upper bound for domains' generation
	 * @param l_coeff
	 *            lower bound for coefficients' generation
	 * @param u_coeff
	 *            upper bound for coefficients' generatio
	 * @param diff
	 *            adjust the difficulty of satisfy each constraint, it defines
	 *            the constant in expression <= cste. cste =
	 *            range_min+(1-diff)*(range_max-range_min) where range is the
	 *            range of the expression.
	 * @param domain2k
	 *            true iff domains' format are [0, 2^k-1], then k is randomly
	 *            chosen between l_dom and u_dom
	 * @param seed
	 * @return a CP Model
	 */
	public static Model[] generateRandomCubicModel(int n, int nc, int m, int l_dom, int u_dom, int l_coeff, int u_coeff,
			double diff, boolean domain2k, long seed) {

		// Init
		Random rnd = new Random(seed);
		Model model = new Model("Random Quadratic Constraints with Decision Diagrams");
		Model model_tree = new Model("Random Linear Constraints with Expression Tree");

		// Generate random domains and insert variables in the model
		int[][] domains;
		if (domain2k) {
			domains = generateRandom2kDomains(model, n, l_dom, u_dom, rnd);
		} else {
			domains = generateRandomDomains(model, n, l_dom, u_dom, rnd);
		}
		HashMap<IntVar, Integer> mapBoolVarIndex = new HashMap<IntVar, Integer>();
		ArrayList<Integer>[] idxBooleanVarLists = addIntegerVariablesDD(model, domains, mapBoolVarIndex, !domain2k);

		// Create integer variables in model_tree
		IntVar[] vars_tree = new IntVar[n];
		for (int i = 0; i < n; i++) {
			vars_tree[i] = model_tree.intVar("x_" + i, domains[i][0], domains[i][1]);
		}

		// Create Random Cubic Constraints
		ArrayList<Integer> ordering = new ArrayList<Integer>();
		ordering.addAll(mapBoolVarIndex.values());
		for (int j = 0; j < nc; j++) {
			// Init DD
			DD dd = new AADD(ordering);

			// Gather all boolean variables used in the constraint
			HashSet<IntVar> boolVarSet = new HashSet<IntVar>();

			// Creation two random expression with a random number of variables
			int[][] randomTerms1 = generateRandomTerms(n, m, l_coeff, u_coeff, rnd);
			int expr1 = generateSumDD(dd, randomTerms1[0], randomTerms1[1], domains, idxBooleanVarLists,
					model.retrieveIntVars(true), boolVarSet);

			int[][] randomTerms2 = generateRandomTerms(n, m, l_coeff, u_coeff, rnd);
			int expr2 = generateSumDD(dd, randomTerms2[0], randomTerms2[1], domains, idxBooleanVarLists,
					model.retrieveIntVars(true), boolVarSet);

			int[][] randomTerms3 = generateRandomTerms(n, m, l_coeff, u_coeff, rnd);
			int expr3 = generateSumDD(dd, randomTerms3[0], randomTerms3[1], domains, idxBooleanVarLists,
					model.retrieveIntVars(true), boolVarSet);

			// Multiply the three expression
			int expr_aux = dd.applyInt(expr1, expr2, DD.ARITH_PROD);
			int expr = dd.applyInt(expr_aux, expr3, DD.ARITH_PROD);

			// Compute bound
			int max = (int) Math.floor(dd.getMaxValue(expr));
			int min = (int) Math.ceil(dd.getMinValue(expr));
			int bound = (int) Math.round(min + (1 - diff) * (max - min));

			// Create arithm constraint
			int ineq = dd.applyInt(expr, dd.getConstantNode(bound), DD.COMP_LESSEQ);
			IntVar[] usedBoolVars = new IntVar[boolVarSet.size()];
			usedBoolVars = boolVarSet.toArray(usedBoolVars);
			Constraint quad = new Constraint("c_" + j, new DDPropagator(usedBoolVars, dd, ineq, mapBoolVarIndex));
			quad.post();

			// Add constraints to model_tree
			int[] coeffs1_tree = new int[n];
			Arrays.fill(coeffs1_tree, 0);
			for (int l = 0; l < m; l++) {
				coeffs1_tree[randomTerms1[0][l]] = randomTerms1[1][l];
			}
			IntVar expr1_tree = model_tree.intVar("expr1", (int) Math.ceil(dd.getMinValue(expr1)),
					(int) Math.floor(dd.getMaxValue(expr1)));
			model_tree.scalar(vars_tree, coeffs1_tree, "=", expr1_tree).post();

			int[] coeffs2_tree = new int[n];
			Arrays.fill(coeffs2_tree, 0);
			for (int l = 0; l < m; l++) {
				coeffs2_tree[randomTerms2[0][l]] = randomTerms2[1][l];
			}
			IntVar expr2_tree = model_tree.intVar("expr2", (int) Math.ceil(dd.getMinValue(expr2)),
					(int) Math.floor(dd.getMaxValue(expr2)));
			model_tree.scalar(vars_tree, coeffs2_tree, "=", expr2_tree).post();

			int[] coeffs3_tree = new int[n];
			Arrays.fill(coeffs3_tree, 0);
			for (int l = 0; l < m; l++) {
				coeffs3_tree[randomTerms3[0][l]] = randomTerms3[1][l];
			}
			IntVar expr3_tree = model_tree.intVar("expr3", (int) Math.ceil(dd.getMinValue(expr3)),
					(int) Math.floor(dd.getMaxValue(expr3)));
			model_tree.scalar(vars_tree, coeffs3_tree, "=", expr3_tree).post();

			IntVar expr_tree_aux = model_tree.intVar("expr_aux", (int) Math.floor(dd.getMinValue(expr_aux)),
					(int) Math.floor(dd.getMaxValue(expr_aux)));
			model_tree.times(expr1_tree, expr2_tree, expr_tree_aux).post();

			IntVar expr_tree = model_tree.intVar("expr", min, bound);
			model_tree.times(expr_tree_aux, expr3_tree, expr_tree).post();

		}

		Model[] models = new Model[2];
		models[0] = model;
		models[1] = model_tree;

		return models;

	}

	
	// ----------------------------------------------------------------
	// ------------------ EXPERIMENTAL EVALUATION----------------------
	// ----------------------------------------------------------------

	private static final int MAX_COEFF = 10;

	// Constant for printing
	final static String[] COLORS = new String[] { "green", "blue", "red", "orange", "purple" };

	// XP Types
	private static final int LINEAR = 0;
	private static final int QUADRATIC = 1;
	private static final int CUBIC = 2;

	// Methods for generating plots in latex
	
	private static <E> String toCoordinate(E[] data) {
		String coordinate = "";
		for (int k = 0; k < data.length; k++) {
			coordinate += "(" + k + "," + data[k] + ")";
		}
		return coordinate;
	}

	private static Object getMaxCoordinates(String orderedCoordinates, boolean isLong) {

		int k = orderedCoordinates.length() - 3;
		while (orderedCoordinates.charAt(k) != ',') {
			k--;
		}

		if (isLong) {
			return Long.parseLong(orderedCoordinates.substring(k + 1, orderedCoordinates.length() - 1));
		} else {
			return Float.parseFloat(orderedCoordinates.substring(k + 1, orderedCoordinates.length() - 1));
		}

	}

	public static void computePlotParameters(int nbInstances, String easyXP[], String mediumXP[], String hardXP[],
			boolean logarithmic) {

		// Computing max coordinates
		ArrayList<Long> max_backtracks = new ArrayList<Long>();
		for (int k = 0; k <= 1; k++) {
			long maxEasy = (long) getMaxCoordinates(easyXP[k], true);
			max_backtracks.add(maxEasy);
			long maxMedium = (long) getMaxCoordinates(mediumXP[k], true);
			max_backtracks.add(maxMedium);
			long maxHard = (long) getMaxCoordinates(hardXP[k], true);
			max_backtracks.add(maxHard);
		}
		long max_backtrack = Math.round(Collections.max(max_backtracks));

		ArrayList<Float> max_times = new ArrayList<Float>();
		for (int k = 2; k <= 3; k++) {
			float maxEasy = (float) getMaxCoordinates(easyXP[k], false);
			max_times.add(maxEasy);
			float maxMedium = (float) getMaxCoordinates(mediumXP[k], false);
			max_times.add(maxMedium);
			float maxHard = (float) getMaxCoordinates(hardXP[k], false);
			max_times.add(maxHard);
		}
		float max_time = (float) (Collections.max(max_times));

		// Display plots latex code

		// data
		String[] nbBacktracks_DD = new String[] { easyXP[0], mediumXP[0], hardXP[0] };
		String[] nbBacktracks_Tree = new String[] { easyXP[1], mediumXP[1], hardXP[1] };
		String[] time_DD = new String[] { easyXP[2], mediumXP[2], hardXP[2] };
		String[] time_Tree = new String[] { easyXP[3], mediumXP[3], hardXP[3] };

		// legends
		String[] legends = new String[] { "easy\\_DD", "medium\\_DD", "hard\\_DD", "easy\\_Tree", "medium\\_Tree",
				"hard\\_Tree" };

		// ytick backtracks
		String ytick_backtrack = "{";
		for (int k = 0; k <= 5; k++) {
			ytick_backtrack += (int) Math.round((k / 5.0) * max_backtrack) + "";
			if (k <= 4) {
				ytick_backtrack += ",";
			}
		}
		ytick_backtrack += "}";

		// ytick times
		String ytick_time = "{";
		for (int k = 0; k <= 5; k++) {
			ytick_time += (k / 5.0) * max_time + "";
			if (k <= 4) {
				ytick_time += ",";
			}
		}
		ytick_time += "}";

		// plots backtrack
		String title_backtrack = "Sorted nb. backtracks for each instance";
		String xlabel = "Instances";
		String ylabel_backtrack = "Nb. backtracks";

		System.out.println("---------------NB BACKTRACKS---------------");
		double ymax_backtrack;
		if (logarithmic) {
			ymax_backtrack = max_backtrack * 2;
		} else {
			ymax_backtrack = 1.05 * max_backtrack;
		}
		generatePlot(logarithmic, nbBacktracks_DD, nbBacktracks_Tree, legends, title_backtrack, xlabel,
				ylabel_backtrack, nbInstances, ymax_backtrack, ytick_backtrack);
		System.out.println();

		String title_Time = "Sorted solving time for each instance";
		String ylabel_Time = "Time (in s)";
		System.out.println("---------------TIMES---------------");
		double ymax_time;
		if (logarithmic) {
			ymax_time = max_time * 2;
		} else {
			ymax_time = 1.05 * max_time;
		}
		generatePlot(logarithmic, time_DD, time_Tree, legends, title_Time, xlabel, ylabel_Time, nbInstances, ymax_time,
				ytick_time);
	}

	public static void generatePlot(boolean logarithmic, String[] data_DD, String[] data_Tree, String[] legends,
			String title, String xlabel, String ylabel, int nbInstances, Number ymax, String ytick) {
		System.out.println("\\begin{tikzpicture}");

		if (logarithmic) {
			System.out.println("\\begin{semilogyaxis}[");
		} else {
			System.out.println("\\begin{axis}[");
		}

		System.out.println("    title={" + title + "}, \n" + "    xlabel={" + xlabel + "}, \n" + "    ylabel={" + ylabel
				+ "}, \n" + "    xmin=0, xmax=" + (nbInstances) + ", \n" + "    ymin=0, ymax=" + ymax + ", \n"
				+ "    legend pos=north west, \n" + "    ymajorgrids=true, \n" + "    grid style=dashed, \n" + "]");

		for (int k = 0; k < data_DD.length; k++) {
			System.out.println(

					"\\addplot[color=" + COLORS[k] + "] \n" + "coordinates {" + data_DD[k] + "}; \n"

			);
		}
		for (int k = 0; k < data_Tree.length; k++) {
			System.out.println(

					"\\addplot[color=" + COLORS[k] + ", dashed] \n" + "coordinates {" + data_Tree[k] + "}; \n"

			);
		}
		String leg = "\\legend{";
		for (int k = 0; k < 2 * data_DD.length; k++) {
			leg += legends[k] + "";
			if (k < 2 * data_DD.length - 1) {
				leg += ",";
			}
		}
		leg += "}";
		System.out.println(leg);
		if (logarithmic) {
			System.out.println("\\end{semilogyaxis});");
		} else {
			System.out.println("\\end{axis});");
		}
		System.out.println("\\end{tikzpicture}");

	}

	// Running experiments with different settings
	
	/**
	 * Generate and run nbInstances problems with the same settings 
	 * and display latex code of plots that compare DDPropagator and 
	 * classic expression tree propagator on these instances.
	 */
	public static String[] xp(int n, int nc, int m, int l, int u, boolean domain2k, double diff, int nbInstances,
			int xpType, boolean logarithmic, long seed) {

		ESat[] sat = new ESat[nbInstances];
		Long[] nbBacktracks_DD = new Long[nbInstances];
		Long[] nbBacktracks_Tree = new Long[nbInstances];
		Float[] time_DD = new Float[nbInstances];
		Float[] time_Tree = new Float[nbInstances];
		long[] time_algoDD = new long[nbInstances];

		Random rnd = new Random(seed);
		for (int i = 0; i < nbInstances; i++) {
			System.out.println((i + 1) + "/" + nbInstances);

			Model[] models;
			switch (xpType) {
			case LINEAR:
				models = generateRandomLinearModel(n, nc, m, l, u, -MAX_COEFF, MAX_COEFF, diff, domain2k,
						rnd.nextLong());
				break;
			case QUADRATIC:
				models = generateRandomQuadraticModel(n, nc, m, l, u, -MAX_COEFF, MAX_COEFF, diff, domain2k,
						rnd.nextLong());
				break;
			case CUBIC:
				models = generateRandomCubicModel(n, nc, m, l, u, -MAX_COEFF, MAX_COEFF, diff, domain2k,
						rnd.nextLong());
				break;
			default:
				models = generateRandomLinearModel(n, nc, m, l, u, -MAX_COEFF, MAX_COEFF, diff, domain2k,
						rnd.nextLong());
			}

			Model model_DD = models[0];
			Model model_Tree = models[1];

			model_DD.getSolver().setSearch(Search.activityBasedSearch(model_DD.retrieveBoolVars()));
			model_Tree.getSolver().setSearch(Search.activityBasedSearch(model_Tree.retrieveIntVars(true)));

			model_DD.getSolver().solve();
			model_Tree.getSolver().solve();

			sat[i] = model_Tree.getSolver().isFeasible();
			nbBacktracks_DD[i] = model_DD.getSolver().getBackTrackCount();
			nbBacktracks_Tree[i] = model_Tree.getSolver().getBackTrackCount();
			if (logarithmic) {
				nbBacktracks_DD[i]++;
				nbBacktracks_Tree[i]++;
			}
			time_DD[i] = model_DD.getSolver().getTimeCount();
			time_Tree[i] = model_Tree.getSolver().getTimeCount();

			time_algoDD[i] = 0;
			for (Constraint c : model_DD.getCstrs()) {
				DDPropagator prop = (DDPropagator) c.getPropagator(0);
				time_algoDD[i] += prop.timeAlgoDD / 1000.0;
			}
		}

		Arrays.sort(nbBacktracks_DD);
		Arrays.sort(nbBacktracks_Tree);
		Arrays.sort(time_DD);
		Arrays.sort(time_Tree);

		String[] coordinates = new String[4];
		coordinates[0] = toCoordinate(nbBacktracks_DD);
		coordinates[1] = toCoordinate(nbBacktracks_Tree);
		coordinates[2] = toCoordinate(time_DD);
		coordinates[3] = toCoordinate(time_Tree);

		return coordinates;

	}

	/**
	 * Call method xp() for problems with binary variables, 
	 * with different settings detailed in the core of the method
	 *
	 */
	public static void xpBinary(int nbInstances, int xpType, boolean logarithmic, long seed) {

		// Generation of results
		int n = 100;
		int nc_easy; int m_easy; double diff_easy;
		int nc_medium; int m_medium; double diff_medium;
		int nc_hard; int m_hard; double diff_hard;

		switch (xpType) {
		case LINEAR:
			nc_easy = 9; m_easy = 9; diff_easy = 0.4;
			nc_medium = 12; m_medium = 12; diff_medium = 0.5;
			nc_hard = 15; m_hard = 15; diff_hard = 0.6;
			break;
		case QUADRATIC:
			nc_easy = 9; m_easy = 4; diff_easy = 0.4;
			nc_medium = 12; m_medium = 6; diff_medium = 0.5;
			nc_hard = 15; m_hard = 8; diff_hard = 0.6;
			break;
		case CUBIC:
			nc_easy = 9; m_easy = 3; diff_easy = 0.4;
			nc_medium = 12; m_medium = 4; diff_medium = 0.5;
			nc_hard = 15; m_hard = 5; diff_hard = 0.6;
			break;
		default:
			nc_easy = 9; m_easy = 9; diff_easy = 0.4;
			nc_medium = 12; m_medium = 12; diff_medium = 0.5;
			nc_hard = 15;m_hard = 15; diff_hard = 0.6;
		}

		System.out.println("EASY INSTANCES");
		String[] easyXP = xp(n, nc_easy, m_easy, 1, 1, true, diff_easy, nbInstances, xpType, logarithmic, seed);

		System.out.println("----------------");
		System.out.println("MEDIUM INSTANCES");
		String[] mediumXP = xp(n, nc_medium, m_medium, 1, 1, true, diff_medium, nbInstances, xpType, logarithmic, seed);

		System.out.println("--------------");
		System.out.println("HARD INSTANCES");
		String[] hardXP = xp(n, nc_hard, m_hard, 1, 1, true, diff_hard, nbInstances, xpType, logarithmic, seed);

		computePlotParameters(nbInstances, easyXP, mediumXP, hardXP, logarithmic);

	}

	/**
	 * Call method xp() for problems with integer variables, 
	 * with different settings detailed in the core of the method
	 *
	 */
	public static void xpInteger(int nbInstances, int xpType, boolean logarithmic, long seed) {

		// Generation of results
		int n = 100;
		int nc_easy; int m_easy; double diff_easy;
		int nc_medium; int m_medium; double diff_medium;
		int nc_hard; int m_hard; double diff_hard;

		switch (xpType) {
		case LINEAR:
			nc_easy = 8; m_easy = 6; diff_easy = 0.4;
			nc_medium = 9; m_medium = 7; diff_medium = 0.5;
			nc_hard = 10; m_hard = 8; diff_hard = 0.6;
			break;
		case QUADRATIC:
			nc_easy = 2; m_easy = 2; diff_easy = 0.3;
			nc_medium = 3; m_medium = 3; diff_medium = 0.4;
			nc_hard = 4; m_hard = 4; diff_hard = 0.5;
			break;
		case CUBIC:
			nc_easy = 9; m_easy = 3; diff_easy = 0.4;
			nc_medium = 12; m_medium = 4; diff_medium = 0.5;
			nc_hard = 15; m_hard = 5; diff_hard = 0.6;
			break;
		default:
			nc_easy = 9; m_easy = 9; diff_easy = 0.4;
			nc_medium = 12; m_medium = 12; diff_medium = 0.5;
			nc_hard = 15; m_hard = 15; diff_hard = 0.6;
		}

		System.out.println("EASY INSTANCES");
		String[] easyXP = xp(n, nc_easy, m_easy, 0, 10, false, diff_easy, nbInstances, xpType, logarithmic, seed);

		System.out.println("----------------");
		System.out.println("MEDIUM INSTANCES");
		String[] mediumXP = xp(n, nc_medium, m_medium, 0, 10, false, diff_medium, nbInstances, xpType, logarithmic,
				seed);

		System.out.println("--------------");
		System.out.println("HARD INSTANCES");
		String[] hardXP = xp(n, nc_hard, m_hard, 0, 10, false, diff_hard, nbInstances, xpType, logarithmic, seed);

		computePlotParameters(nbInstances, easyXP, mediumXP, hardXP, logarithmic);

	}

	/**
	 * Call method xp() for problems with integer variables 
	 * with domain size equals to 2^k, with different settings 
	 * detailed in the core of the method
	 *
	 */
	public static void xpInteger2k(int nbInstances, int xpType,
			boolean logarithmic, long seed) {
		// Generation of results
		int n = 100;
		int nc_easy; int m_easy; double diff_easy;
		int nc_medium; int m_medium; double diff_medium;
		int nc_hard; int m_hard; double diff_hard;
		int k;

		switch (xpType) {
		case LINEAR:
			nc_easy = 8; m_easy = 6; diff_easy = 0.4;
			nc_medium = 10; m_medium = 7; diff_medium = 0.5;
			nc_hard = 12; m_hard = 8; diff_hard = 0.6;
			k=3;
			break;
		case QUADRATIC:
			nc_easy = 5; m_easy = 2; diff_easy = 0.4;
			nc_medium = 6; m_medium = 3; diff_medium = 0.5;
			nc_hard = 7; m_hard = 4; diff_hard = 0.6;
			k=3;
			break;
		case CUBIC:
			nc_easy = 2; m_easy = 2; diff_easy = 0.3;
			nc_medium = 3; m_medium = 3; diff_medium = 0.4;
			nc_hard = 4; m_hard = 4; diff_hard = 0.5;
			k=2;
			break;
		default:
			nc_easy = 9; m_easy = 9; diff_easy = 0.4;
			nc_medium = 12; m_medium = 12; diff_medium = 0.5;
			nc_hard = 15; m_hard = 15; diff_hard = 0.6;
			k=3;
		}

		System.out.println("EASY INSTANCES");
		String[] easyXP = xp(n, nc_easy, m_easy, k,k, true, diff_easy, nbInstances, xpType, logarithmic, seed);

		System.out.println("----------------");
		System.out.println("MEDIUM INSTANCES");
		String[] mediumXP = xp(n, nc_medium, m_medium, k, k, true, diff_medium, nbInstances, xpType, logarithmic,
				seed);

		System.out.println("--------------");
		System.out.println("HARD INSTANCES");
		String[] hardXP = xp(n, nc_hard, m_hard, k, k, true, diff_hard, nbInstances, xpType, logarithmic, seed);

		computePlotParameters(nbInstances, easyXP, mediumXP, hardXP, logarithmic);
	}


	public static void main(String[] args) {

		xpInteger2k(100, CUBIC, true, 202106010043L);

	}

}