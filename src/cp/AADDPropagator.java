package cp;

import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.ESat;

/**
 * 
 * Propagator of an AADD (Affine Algebraic Decision Diagram) constraint
 * 
 * 
 * @author giovannilobianco
 *
 */
public class AADDPropagator extends Propagator<IntVar>{

	@Override
	public void propagate(int evtmask) throws ContradictionException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public ESat isEntailed() {
		// TODO Auto-generated method stub
		return null;
	}

}
