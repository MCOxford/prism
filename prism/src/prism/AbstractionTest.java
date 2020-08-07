package prism;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.HashMap;
import java.util.Map;
import java.util.LinkedList;
import java.util.Vector;

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
	private double epsilon = 10e-14; 
	
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
		// Attach evaluator and variable info
        //((ModelExplicit<Value>) modelSimple).setEvaluator(modelGen.getEvaluator());
        //((ModelExplicit<Value>) modelSimple).setVarList(varList);
		
		// Initialise states storage
		// TODO: Is there a way to do this without the IndexedSet?
		states = new IndexedSet<State>(true);
		absStates = new IndexedSet<State>(true);
		explore = new LinkedList<State>();
		// Add initial state to 'explore', 'states' and to the model
		// (For now, it must be unique)
		if (!modelGen.hasSingleInitialState()) {
			//throw new Exception("Number of initial states in concrete model must not exceed one.");
		}
		State initState = modelGen.getInitialState();
		explore.add(initState);
		states.add(initState);
		model.addState();
		model.addInitialState(model.getNumStates() - 1);
		// Explore...
		absSrc = -1;
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
			absSrc++;
			System.out.println(currentAbsState);
			// Has currentAbsState already been added to ADTMC?
			if (!absStates.add(currentAbsState)) {
				// Something here...
			}
			else {
				// Otherwise, add it to the model
				model.addState();
				for(State nextAbsState : distr.keySet()) {
					if (absStates.add(nextAbsState)) {
						//System.out.println("ding");
						dest = absStates.getIndexOfLastAdd();
						model.addState();
						System.out.println(absSrc);
						System.out.println(absStates);
						System.out.println(dest);
						//System.out.println(new Interval<Double>(distr.get(nextAbsState), distr.get(nextAbsState)));
						double prob = distr.get(nextAbsState);
						model.addToProbability(absSrc, dest, new Interval<Double>(prob, prob));
					}
				}
			System.out.println(absStates);
			}
		}
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
			State state = modelGen.getInitialState();
			//System.out.println("Initial state: " + state);
			//System.out.println("Abstract variable state: " + findAbsState(state));
			
			// Examine successor states
			modelGen.exploreState(state);
			int numTransitions = modelGen.getNumTransitions(0);
			for (int i = 0; i < numTransitions; i++) {
				state = modelGen.computeTransitionTarget(0, i);
				//System.out.println("Successor state: " + state);
				//System.out.println("Abstract variable state: " + findAbsState(state));
			}
			
			// Construct abstract model and print
			//constructAbsModel(modelGen);
			//System.out.print(model);
			
			IDTMCSimple<Double> imc = new IDTMCSimple<>();
			imc.addState();
			// THIS IS NOT WORKING
			imc.addToProbability(0, 1, new Interval<Double>(0.0, 1.0));
			
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
