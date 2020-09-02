/**
 * 2020- mco, dxp
 */
package prism;

import java.io.*;

import java.util.HashMap;
import java.util.Map;
import java.util.LinkedList;
import java.util.Vector;
import java.util.Set;
import java.util.HashSet;
import java.util.BitSet;
import java.util.List;
import java.util.ArrayList;

import explicit.Distribution;
import explicit.IDTMCSimple;
import explicit.IDTMCModelChecker;
import explicit.IndexedSet;
import explicit.MinMax;
import explicit.ModelCheckerResult;
import explicit.StateStorage;

import parser.State;
import parser.ast.Expression;
import parser.ast.FormulaList;
import parser.ast.LabelList;
import parser.ast.ModulesFile;
import parser.VarList;
import parser.type.*;

import common.Interval;

public class AbstractionTest
{
	// List of abstract variable names
	protected Vector<String> absVarNames = new Vector<String>();
	// List of abstract variable formulae. Should match up pair wise with absVarNames elements.
	protected Vector<Expression> absVarExps = new Vector<Expression>();
	// ADTMC to be constructed
	protected IDTMCSimple<Double> model = new IDTMCSimple<>();
	// Set of abstract states;
	protected List<State> statesList;
	// Target set of States
	protected Expression labelExp = null;
	protected List<Integer> targets = new ArrayList<Integer>();
	// A very small value close to zero
	private static double epsilon = Double.MIN_VALUE; 
	// timer
	private static long timer;
	// List of (concrete variables)
	private VarList variableList;
	// Iterating state
	protected State enumerateState;
	// index of enumerateState
	protected int index = 0;
	
	/**
	 * Find Abstract variables names and formulae and add them to vectors absVarNames
	 * and absVarExps, respectively. Abstract formula names must start with "abs_" to be counted.
	 * @param formulaList The list of formulae from concrete model
	 */
	public void findAbsFormulaList(FormulaList formulaList)
	{
		for (int i = 0; i < formulaList.size(); i++) {
			String formulaName = formulaList.getFormulaName(i);
			if (formulaName.startsWith("abs_")) {
				String abstractVar = formulaName.substring(4);
				if(!absVarNames.contains(abstractVar)) {
					absVarNames.addElement(abstractVar);
					absVarExps.addElement(formulaList.getFormula(i));
				}
			}
		}
	}
	
	/**
	 * For a given concrete state, find the corresponding abstract state
	 * @param concreteState state from original model
	 */
	public State findAbsState(State concreteState) throws PrismLangException
	{
		int size = absVarNames.size();
		State absState = new State(size);
		for (int i = 0; i < size; i++) {
			Expression exp = absVarExps.elementAt(i);
			absState.setValue(i, exp.evaluate(concreteState));
		}
		return absState;
	}
	
	/**
	 * Export target set to file
	 * @param filename file name to export to
	 * @throws IOException 
	 */
	public void exportTargetSet(String filename) throws PrismException, IOException
	{
		FileOutputStream out = null;
		try {
			out = new FileOutputStream(filename);
			BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(out));
			for (Integer target : targets) {
				bw.write(target.toString());
				bw.newLine();
			}
			bw.close();
		} catch (IOException e) {
			System.out.println("File not found: " + e);
		}
	}
	
	/**
	 * Reset timer
	 */
	public void resetTimer() {
		timer = System.currentTimeMillis();
	}

	/**
	 * Compute total amount of time elapsed (in seconds). Assume that
	 * timer has been initialised
	 */
	public double computeTime() {
		return (System.currentTimeMillis() - timer) / 1000.0;
	}
	
	/**
	 * Use enumerateState to go to the next possible state (reachable from the
	 * initial state or otherwise
	 */
	public void toNextState() {
		int newIndex = 0;
		for (int i = index; i >= 0; i--) {
			if (variableList.getType(i) instanceof TypeBool) {
				if (i == index) {
					enumerateState.setValue(i, true);
				} else {
					enumerateState.setValue(i, false);
				}
			} else if (variableList.getType(i) instanceof TypeInt) {
				int lo = variableList.getLow(i);
				if (i == index) {
					enumerateState.setValue(i, (Integer) enumerateState.varValues[i] + 1);
				} else {
					enumerateState.setValue(i, lo);
				}
			}
		}
		for (int j = 0; j < variableList.getNumVars(); j++) {
			if (variableList.getType(j) instanceof TypeBool) {
				if ((Boolean) enumerateState.varValues[j] == true) {
					newIndex++;
				}
				else {
					break;
				}
			} else if (variableList.getType(j) instanceof TypeInt) {
				int hi = variableList.getHigh(j);
				if ((Integer) enumerateState.varValues[j] == hi) {
					newIndex++;
				} 
				else {
					break;
				}
			}
		}
		index = newIndex;
	}
	
	public Interval<Double> addition(Interval<Double> i1, Interval<Double> i2) {
		return new Interval<Double>(i1.getLower() + i2.getLower(), Math.min(1, i1.getUpper() + i2.getUpper()));
	}
	
	/**
	 * Construct Abstract DTMC (This method works similarly to ConstructModel.java)
	 * @param modelGen The ModelGenerator interface providing the (concrete) model
	 */
	public void constructAbsModel(ModelGenerator<?> modelGen) throws PrismException {
		// Model info
		ModelType modelType;
		// distr is used in the process of abstracting DTMCs, distrInt for IDTMCs
		Map<State, Double> distr = new HashMap<State, Double>();
		Map<State, Interval<Double>> distrInt = new HashMap<State, Interval<Double>>();;
		// State storage
		StateStorage<State> states;
		StateStorage<State> absStates;
		LinkedList<State> explore;
		State state, stateNew;
		// Misc
		int i, absSrc, dest;
		int nt = 1;

		// Get model info
		modelType = modelGen.getModelType();
		System.out.println(modelType);

		// Create a (simple, mutable) model of the appropriate type
		switch (modelType) {
		case DTMC:
		case IDTMC:
			break;
		case CTMC: // MIC: Would make a good future mini-project to abstract CTMCs using this code
		case MDP:
		case CTMDP:
		case STPG:
		case SMG:
		case PTA:
		case LTS:
			throw new PrismNotSupportedException("Code not supported for " + modelType + "s");
		}
		// Create evaluator for model
		model.setEvaluator(Evaluator.createForDoubleIntervals());
		// Initialise states storage
		states = new IndexedSet<State>(true);
		absStates = new IndexedSet<State>(true);
		explore = new LinkedList<State>();
		// Add initial state to 'explore', 'states' and to the model
		// (For now, it must be unique)
		if (!modelGen.hasSingleInitialState()) {
			throw new PrismException("Error: dtmc must have a unique initial state");
		}
		State initState = modelGen.getInitialState();
		explore.add(initState);
		states.add(initState);
		model.addState();
		model.addInitialState(model.getNumStates() - 1);
		// Explore...
		while (!explore.isEmpty()) {
			// Pick next state to explore
			// (they are stored in order found so know index is src+1)
			state = explore.removeFirst();
			// Explore all transitions from this state
			modelGen.exploreState(state);
			// Create set of successor states
			StateStorage<State> nextStates = new IndexedSet<State>(true);
			if (modelType == ModelType.DTMC) {
				distr = new HashMap<State, Double>();
			}
			if (modelType == ModelType.IDTMC) {
				distrInt = new HashMap<State, Interval<Double>>();
			}
			// If state is a deadlock, add a self-loop and continue
			if (modelGen.isDeadlock()) {
				nextStates.add(state);
				if (modelType == ModelType.DTMC) {
					distr.put(state, 1.0);
				}
				if (modelType == ModelType.IDTMC) {
					distrInt.put(state, new Interval<Double>(1.0, 1.0));
				}
			}
			else {
				nt = modelGen.getNumTransitions(0);
				for (i = 0; i < nt; i++) {
					stateNew = modelGen.computeTransitionTarget(0, i);
					// Is this a new state?
					if (states.add(stateNew)) {
						// If so, add to the explore list
						explore.add(stateNew);
					}
					// Find which abstract state (concrete) stateNew maps to
					State absState = findAbsState(stateNew);
					if (modelType == ModelType.DTMC) {
						double prob = (double) modelGen.getTransitionProbability(0, i);
						// Has a new (abstract) successor state been found?
						if (nextStates.add(absState)) {
							// If so, extend probability distribution with new information
							distr.put(absState, prob);
						}
						else {
							distr.put(absState, distr.get(absState) + prob);
						}
					}
					if (modelType == ModelType.IDTMC) {
						Interval<Double> prob = (Interval<Double>) modelGen.getTransitionProbability(0, i);
						if (nextStates.add(absState)) {
							distrInt.put(absState, prob);
						}
						else {
							distrInt.put(absState, addition(distrInt.get(absState), prob));
						}
					}
				}
			}
			// Now, find the abstract state we are currently exploring using state
			State currentAbsState = findAbsState(state);
			// Has currentAbsState present in the ADTMC?
			if (absStates.add(currentAbsState)) {
				// Get index of source (abstract) state
				absSrc = absStates.getIndexOfLastAdd();
				// If not and it is not the initial state, add it to the model
				if (!model.isInitialState(absSrc)) {
					model.addState();
				}
				if (modelType == ModelType.DTMC) {
					for(State nextAbsState : distr.keySet()) {
						// if nextAbsState not in model, add it
						if (absStates.add(nextAbsState)) {
							model.addState();
						}
						// Get index of destination (abstract) state, add transition with interval
						dest = absStates.getIndexOfLastAdd();
						double prob = distr.get(nextAbsState);
						model.addToProbability(absSrc, dest, new Interval<Double>(prob, prob));
					}
				}
				if (modelType == ModelType.IDTMC) {
					for(State nextAbsState : distrInt.keySet()) {
						// if nextAbsState not in model, add it
						if (absStates.add(nextAbsState)) {
							model.addState();
						}
						// Get index of destination (abstract) state, add transition with interval
						dest = absStates.getIndexOfLastAdd();
						Interval<Double> prob = distrInt.get(nextAbsState);
						model.addToProbability(absSrc, dest, prob);
					}
				}
			}
			else {
				absSrc = absStates.getIndexOfLastAdd();
				// Get support of absSrc
				Set<Integer> disSupport = new HashSet<Integer>(model.getTransitions(absSrc).getSupport());
				Distribution<Interval<Double>> dis = new Distribution<Interval<Double>>(model.getTransitions(absSrc));
				if (modelType == ModelType.DTMC) {
					for(State nextAbsState : distr.keySet()) {
						// if nextAbsState not in model, add it
						if (absStates.add(nextAbsState)) {
							model.addState();
						}
						// Get index of destination (abstract) state and distribution of absSrc
						dest = absStates.getIndexOfLastAdd();
						// if distribution contains dest, update lower/upper bound of interval
						if (dis.contains(dest)) {
							double lower = Math.min(dis.get(dest).getLower(), distr.get(nextAbsState));
							double upper = Math.max(dis.get(dest).getUpper(), distr.get(nextAbsState));
							model.setProbability(absSrc, dest, new Interval<Double>(lower, upper));
						}
						else {
							double lower = distr.get(nextAbsState);
							double upper = distr.get(nextAbsState);
							// If distribution is non-empty, there exists concrete states that do not
							// go to states represented by dest i.e. change lower bound to be (close to)
							// zero
							if (dis.size() > 0) {
								lower = epsilon;
							}
							// Finally, add state and interval to distribution
							model.addToProbability(absSrc, dest, new Interval<Double>(lower, upper));
						}
						// If disSupport contains dest, remove it
						disSupport.remove(dest);
					}
				}
				if (modelType == ModelType.IDTMC) {
					for(State nextAbsState : distrInt.keySet()) {
						// if nextAbsState not in model, add it
						if (absStates.add(nextAbsState)) {
							model.addState();
						}
						// Get index of destination (abstract) state and distribution of absSrc
						dest = absStates.getIndexOfLastAdd();
						// if distribution contains dest, update lower/upper bound of interval
						if (dis.contains(dest)) {
							double lower = Math.min(dis.get(dest).getLower(), distrInt.get(nextAbsState).getLower());
							double upper = Math.max(dis.get(dest).getUpper(), distrInt.get(nextAbsState).getUpper());
							model.setProbability(absSrc, dest, new Interval<Double>(lower, upper));
						}
						else {
							double lower = distrInt.get(nextAbsState).getLower();
							double upper = distrInt.get(nextAbsState).getUpper();
							// If distribution is non-empty, there exists concrete states that do not
							// go to states represented by dest i.e. change lower bound to be (close to)
							// zero
							if (dis.size() > 0) {
								lower = epsilon;
							}
							// Finally, add state and interval to distribution
							model.addToProbability(absSrc, dest, new Interval<Double>(lower, upper));
						}
						// If disSupport contains dest, remove it
						disSupport.remove(dest);
					}
				}
				// For states that do exist in the support of absSrc but not in distr, change the lower
				// bounds of the respective intervals to zero. 
				for (int j : disSupport) {
					model.setProbability(absSrc, j, new Interval<Double>(epsilon, dis.get(j).getUpper()));
				}
			}
			// Add absSrc to the target set if abs_t evaluates to true for state
			if (labelExp.evaluateBoolean(state) && !targets.contains(absSrc)) {
				targets.add(absSrc);
			}
		}
		states.clear();
		states = null;
		// Print out unordered index set of abstract states (for debugging purposes only) 
//		System.out.println(absStates);
	}
	
	/**
	 * Test method for demonstration purposes
	 * @param args (first element must be path to a PRISM model)
	 * @throws IOException 
	 */
	public void run(String[] args) throws IOException
	{
		int ROUND_NUMBER = 4;
		
		try {
			// Create a log for PRISM output (hidden or stdout)
			PrismLog mainLog = new PrismDevNullLog();
			//PrismLog mainLog = new PrismFileLog("stdout");

			// Initialise PRISM engine 
			Prism prism = new Prism(mainLog);
			prism.initialise();

			// Parse and load a PRISM model from a file
			ModulesFile modulesFile = prism.parseModelFile(new File(args[0]));
			prism.loadPRISMModel(modulesFile);

			// Extract abstract variables from formulas
			FormulaList formulaList = modulesFile.getFormulaList();
			findAbsFormulaList(formulaList);
			System.out.println("\nAbstract variable names and expressions:");
			for (int i = 0; i < absVarNames.size(); i++) {
				System.out.println("(" + absVarExps.get(i).getType() + ") " + absVarNames.get(i) + " = " + absVarExps.get(i));
			}
			
			// Extract expression for label "abs_t"
			LabelList labelList = modulesFile.getLabelList();
			int ind = labelList.getLabelIndex("abs_t");
			if (ind == -1) {
				System.out.println("\nError: abs_t label not found");
				System.exit(1);
			}
			labelExp = labelList.getLabel(ind);
			System.out.println("\nTarget set conditions:\n" + labelExp);
			
			// Get model generator for PRISM model
			prism.loadPRISMModel(modulesFile);
			ModelGenerator<?> modelGen = prism.getModelGenerator();
			
			// Initialise enumerated state
//			variableList = new VarList(modelGen);
//			int numVars = variableList.getNumVars();
//			enumerateState = new State(numVars);
//			for(int i=0; i < numVars; i++) {
//				if (variableList.getType(i) instanceof TypeBool) {
//					enumerateState.setValue(i, false);
//				} else if (variableList.getType(i) instanceof TypeInt) {
//					int lo = variableList.getLow(i);
//					int hi = variableList.getHigh(i);
//					enumerateState.setValue(i, lo);
//				}
//			}
			
			// Examine initial state
//			State state = modelGen.getInitialState();
//			System.out.println("Initial state: " + state);
//			System.out.println("Abstract variable state: " + findAbsState(state));
			
			// Examine successor states
//			modelGen.exploreState(state);
//			int numTransitions = modelGen.getNumTransitions(0);
//			for (int i = 0; i < numTransitions; i++) {
//				state = modelGen.computeTransitionTarget(0, i);
//				System.out.println("Successor state: " + state);
//				System.out.println("Abstract variable state: " + findAbsState(state));
//			}
			
			// Construct abstract model and print
			System.out.println("\nConstructing ADTMC model...");
			timer = System.currentTimeMillis();
			constructAbsModel(modelGen);
			double time = computeTime();
			System.out.println("\nType:\t\t" + model.getModelType() + "\nStates:\t\t" + model.getNumStates() + "\nTransitions:\t" + model.getNumTransitions());
			System.out.println("\nTime for model construction: " + time + " seconds.");
			
			// Set states in targetsBit to true if in targets
			BitSet targetsBit = new BitSet(model.getNumStates());
			for (int i = 0; i < model.getNumStates(); i++) {
				if (targets.contains(i)) {
					targetsBit.set(i);
				}
			}
			
			// Export model information (for debugging purposes only)
//			System.out.println(model);
//			model.exportToPrismExplicitTra(args[1]);
//			exportTargetSet(args[2]);
//			model.exportToDotFile(args[3], targetsBit);
//			System.out.println("...done\n");
			
			IDTMCModelChecker mc = new IDTMCModelChecker(prism);

			System.out.print("\nComputing minimal bounded reachability...\n");
			for (int i = 1; i <= 20; i++) {
				resetTimer();
				ModelCheckerResult mcRes = mc.computeBoundedReachProbs(model, targetsBit, 4*i, MinMax.min());
				double roundTime = computeTime();
				System.out.println("Round " + i + " (" + ROUND_NUMBER*i + " steps): " + mcRes.soln[0] + "\t(" + roundTime + "s)");
			}
			
			System.out.print("\nComputing maximal bounded reachability...\n");
			for (int i = 1; i <= 20; i++) {
				resetTimer();
				ModelCheckerResult mcRes = mc.computeBoundedReachProbs(model, targetsBit, 4*i, MinMax.max());
				double roundTime = computeTime();
				System.out.println("Round " + i + " (" + ROUND_NUMBER*i + " steps): " + mcRes.soln[0] + "\t(" + roundTime + "s)");
			}
		
			// Close down PRISM
			prism.closeDown();

		} catch (FileNotFoundException e) {
			System.out.println("Error: " + e.getMessage());
			System.exit(1);
		} catch (PrismException e) {
			System.out.println("Error: " + e.getMessage());
			System.exit(1);
		}
	}
	
	public static void main(String[] args) throws IOException
	{
		new AbstractionTest().run(args);
	}

}
