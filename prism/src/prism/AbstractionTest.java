package prism;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.HashMap;
import java.util.Map;
import java.util.LinkedList;
import java.util.Vector;
import java.util.Set;
import java.util.HashSet;

import explicit.Distribution;
import explicit.IDTMCSimple;
import explicit.IndexedSet;
import explicit.StateStorage;
import parser.State;
import parser.ast.Expression;
import parser.ast.FormulaList;
import parser.ast.ModulesFile;

import common.Interval;

public class AbstractionTest
{
	// List of abstract variable names
	private Vector<String> absVarNames = new Vector<String>();
	// List of abstract variable formulae. Should match up pair wise with absVarNames elements.
	private Vector<Expression> absVarExps = new Vector<Expression>();
	// ADTMC to be constructed
	private IDTMCSimple<Double> model = new IDTMCSimple<>();
	// A very small value close to zero
	private static double epsilon = 1e-14; 
	
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
	 * Construct Abstract DTMC (This method works similarly to ConstructModel.java)
	 * @param modelGen The ModelGenerator interface providing the (concrete) model
	 * @return IDTMC model
	 */
	public void constructAbsModel(ModelGenerator<?> modelGen) throws PrismException
	{
		// Model info
		ModelType modelType;
		// State storage
		StateStorage<State> states;
		StateStorage<State> absStates;
		LinkedList<State> explore;
		State state, stateNew;
		// Misc
		int i, nt, absSrc, dest;
		//long timer;

		// Get model info
		modelType = modelGen.getModelType();
		
		// Display a warning if there are unbounded vars
		//VarList varList = modelGen.createVarList();
		//if (modelGen.containsUnboundedVariables())
			//mainLog.printWarning("Model contains one or more unbounded variables: model construction may not terminate");

		// Starting reachability...
		//mainLog.print("\nComputing reachable states...");
		//mainLog.flush();
		//ProgressDisplay progress = new ProgressDisplay(mainLog);
		//progress.start();
		//timer = System.currentTimeMillis();

		// Create a (simple, mutable) model of the appropriate type
		switch (modelType) {
		case DTMC:
			break;
		case CTMC: // MIC: Would make a good future mini-project if CTMCs could be abstract in some way.
		case MDP:
		case CTMDP:
		case IDTMC:
		case STPG:
		case SMG:
		case PTA:
		case LTS:
			throw new PrismNotSupportedException("Code not supported for " + modelType + "s");
		}
		// Create evaluator for model
		model.setEvaluator(Evaluator.createForDoubleIntervals());
		// Initialise states storage
		// TODO: Is there a way to do this without the IndexedSet?
		states = new IndexedSet<State>(true);
		absStates = new IndexedSet<State>(true);
		explore = new LinkedList<State>();
		// Add initial state to 'explore', 'states' and to the model
		// (For now, it must be unique)
		if (!modelGen.hasSingleInitialState()) {
			// TODO: Throw exception if there is more than one initial state
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
			nt = modelGen.getNumTransitions(0);
			// Create set of successor states
			StateStorage<State> nextStates = new IndexedSet<State>(true);
			Map<State, Double> distr = new HashMap<State, Double>();
			for (i = 0; i < nt; i++) {
					stateNew = modelGen.computeTransitionTarget(0, i); // TODO: If deadlocks are present, fix it.
					// Is this a new state?
					if (states.add(stateNew)) {
						// If so, add to the explore list
						explore.add(stateNew);
					}
					// Find which abstract state (concrete) stateNew maps to
					State absState = findAbsState(stateNew);
					// Has a new (abstract) successor state been found?
					double prob = (double) modelGen.getTransitionProbability(0, i);
					if (nextStates.add(absState)) {
						// If so, extend probability distribution with new information
						distr.put(absState, prob);
					}
					else {
						// Otherwise, update existing probability distribution with new information
						distr.put(absState, distr.get(absState) + prob);
					}
			}
			// Now, find the abstract state we are currently exploring using state
			State currentAbsState = findAbsState(state);
			// Has currentAbsState present in the ADTMC?
			//System.out.println("current: " + currentAbsState);
			//System.out.println("distr: " + distr);
			if (absStates.add(currentAbsState)) {
				absSrc = absStates.getIndexOfLastAdd();
				//System.out.println("absSrc: " + absSrc);
				// If not and it is not the initial state, add it to the model
				if (!model.isInitialState(absSrc)) {
					model.addState();
				}
				//System.out.println("size: " + model.getNumStates());
				// Get index of source (abstract) state
				absSrc = absStates.getIndexOfLastAdd();
				for(State nextAbsState : distr.keySet()) {
					// if nextAbsState not in model, add it
					if (absStates.add(nextAbsState)) {
						model.addState();
						//System.out.println("size: " + model.getNumStates());
					}
					// Get index of destination (abstract) state, add transition w/ interval
					dest = absStates.getIndexOfLastAdd();
					double prob = distr.get(nextAbsState);
					model.addToProbability(absSrc, dest, new Interval<Double>(prob, prob));
				}
			}
			else {
				absSrc = absStates.getIndexOfLastAdd();
				//System.out.println("absSrc: " + absSrc);
				//System.out.println(absStates.getEntrySet());
				Set<Integer> scannedStates = new HashSet<Integer>();
				for(State nextAbsState : distr.keySet()) {
					if (absStates.add(nextAbsState)) {
						model.addState();
					}
					dest = absStates.getIndexOfLastAdd();
					Distribution<Interval<Double>> dis = model.getTransitions(absSrc);
					if (dis.contains(dest)) {
						double lower = Math.min(dis.get(dest).getLower(), distr.get(nextAbsState));
						double upper = Math.max(dis.get(dest).getUpper(), distr.get(nextAbsState));
						model.setProbability(absSrc, dest, new Interval<Double>(lower, upper));
					}
					else {
						double lower;
						double upper = distr.get(nextAbsState);
						if (model.getTransitions(absSrc).size() > 0) {
							lower = epsilon;
						}
						else {
							lower = distr.get(nextAbsState);
						}
						model.addToProbability(absSrc, dest, new Interval<Double>(lower, upper));
					}
					scannedStates.add(dest);
				}
				Set<Integer> disSupport = new HashSet<Integer>(model.getTransitions(absSrc).getSupport());
				disSupport.removeAll(scannedStates);
				Distribution<Interval<Double>> dis = model.getTransitions(absSrc);
				for (int j : disSupport) {
					model.setProbability(absSrc, j, new Interval<Double>(epsilon, dis.get(j).getUpper()));
				}
			}
			//System.out.println(model);
		}
		//System.out.println(absStates);
	}
	
	/**
	 * Test method for demonstration purposes
	 * @param args first element must be path to a PRISM model
	 */
	public void run(String[] args)
	{
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
			System.out.println(absVarNames);
			System.out.println(absVarExps);
			
			// Get model generator for PRISM model
			prism.loadPRISMModel(modulesFile);
			ModelGenerator<?> modelGen = prism.getModelGenerator();
			
			// Examine initial state
			//State state = modelGen.getInitialState();
			//System.out.println("Initial state: " + state);
			//System.out.println("Abstract variable state: " + findAbsState(state));
			
			// Examine successor states
			//modelGen.exploreState(state);
			//int numTransitions = modelGen.getNumTransitions(0);
			//for (int i = 0; i < numTransitions; i++) {
				//state = modelGen.computeTransitionTarget(0, i);
				//System.out.println("Successor state: " + state);
				//System.out.println("Abstract variable state: " + findAbsState(state));
			//}
			
			// Construct abstract model and print
			constructAbsModel(modelGen);
			System.out.println(model);

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
	
	public static void main(String[] args)
	{
		new AbstractionTest().run(args);
	}

}
