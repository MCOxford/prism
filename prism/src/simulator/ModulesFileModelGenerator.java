package simulator;

import java.util.ArrayList;
import java.util.List;

import parser.State;
import parser.Values;
import parser.VarList;
import parser.ast.DeclarationType;
import parser.ast.Expression;
import parser.ast.LabelList;
import parser.ast.ModulesFile;
import parser.ast.RewardStruct;
import parser.type.Type;
import prism.Evaluator;
import prism.ModelGenerator;
import prism.ModelType;
import prism.PrismComponent;
import prism.PrismException;
import prism.PrismLangException;
import prism.RewardGenerator;

public class ModulesFileModelGenerator<Value> implements ModelGenerator<Value>, RewardGenerator<Value>
{
	// Parent PrismComponent (logs, settings etc.)
	protected PrismComponent parent;
	
	// Evaluator for values/states
	protected Evaluator<Value> eval;
	
	// PRISM model info
	/** The original modules file (might have unresolved constants) */
	protected ModulesFile originalModulesFile;
	/** The modules file used for generating (has no unresolved constants after {@code initialise}) */
	protected ModulesFile modulesFile;
	protected ModelType modelType;
	protected Values mfConstants;
	protected VarList varList;
	protected LabelList labelList;
	protected List<String> labelNames;
	
	// Model exploration info
	
	// State currently being explored
	protected State exploreState;
	// Updater object for model
	protected Updater<Value> updater;
	// List of currently available transitions
	protected TransitionList<Value> transitionList;
	// Has the transition list been built? 
	protected boolean transitionListBuilt;
	
	/**
	 * Build a ModulesFileModelGenerator for a particular PRISM model, represented by a {@link ModulesFile} instance.
	 * An {@link Evaluator} of the appropriate type is created.
	 * So, this static creator method should generally be preferred to calling the constructors directly.
	 * Throw an explanatory exception if this is not possible.
	 * @param modulesFile The PRISM model
	 * @param parent Parent, used e.g. for settings (can be null)
	 */
	public static ModulesFileModelGenerator<?> create(ModulesFile modulesFile, PrismComponent parent) throws PrismException
	{
		// For now, we just create an Evaluator<Double>
		Evaluator<Double> evalDbl = Evaluator.createForDoubles();
		return new ModulesFileModelGenerator<Double>(modulesFile, evalDbl, parent);
	}
	
	/**
	 * Build a ModulesFileModelGenerator for a particular PRISM model, represented by a {@link ModulesFile} instance.
	 * Creates a default {@link Evaluator}{@code <Double>} so only works for {@code ModulesFileModelGenerator<Double>}.
	 * Throw an explanatory exception if this is not possible.
	 * @param modulesFile The PRISM model
	 */
	public ModulesFileModelGenerator(ModulesFile modulesFile) throws PrismException
	{
		this(modulesFile, (PrismComponent) null);
	}
	
	/**
	 * Build a ModulesFileModelGenerator for a particular PRISM model, represented by a {@link ModulesFile} instance.
	 * Throw an explanatory exception if this is not possible.
	 * Creates a default {@link Evaluator}{@code <Double>} so only works for {@code ModulesFileModelGenerator<Double>}.
	 * @param modulesFile The PRISM model
	 * @param parent Parent, used e.g. for settings (can be null)
	 */
	@SuppressWarnings("unchecked")
	public ModulesFileModelGenerator(ModulesFile modulesFile, PrismComponent parent) throws PrismException
	{
		this(modulesFile, (Evaluator<Value>) Evaluator.createForDoubles(), parent);
	}
	
	/**
	 * Build a ModulesFileModelGenerator for a particular PRISM model, represented by a {@link ModulesFile} instance.
	 * Takes in an {@link Evaluator}{@code <Value>} to match the type parameter {@code Value} of this class.
	 * Throw an explanatory exception if this is not possible.
	 * @param modulesFile The PRISM model
	 * @param eval Evaluator matching the type parameter {@code Value} of this class
	 * @param parent Parent, used e.g. for settings (can be null)
	 */
	public ModulesFileModelGenerator(ModulesFile modulesFile, Evaluator<Value> eval, PrismComponent parent) throws PrismException
	{
		this.parent = parent;
		this.eval = eval;
		
		// No support for PTAs yet
		if (modulesFile.getModelType() == ModelType.PTA) {
			throw new PrismException("PTAs are not currently supported");
		}
		// No support for system...endsystem yet
		if (modulesFile.getSystemDefn() != null) {
			throw new PrismException("The system...endsystem construct is not currently supported");
		}
		
		// Store basic model info
		this.modulesFile = modulesFile;
		this.originalModulesFile = modulesFile;
		modelType = modulesFile.getModelType();
		
		// If there are no constants to define, go ahead and initialise;
		// Otherwise, setSomeUndefinedConstants needs to be called when the values are available  
		mfConstants = modulesFile.getConstantValues();
		if (mfConstants != null) {
			initialise();
		}
	}
	
	/**
	 * (Re-)Initialise the class ready for model exploration
	 * (can only be done once any constants needed have been provided)
	 */
	private void initialise() throws PrismException
	{
		// Evaluate constants on (a copy) of the modules file, insert constant values
		modulesFile = (ModulesFile) modulesFile.deepCopy().replaceConstants(mfConstants);
		// Optimise arithmetic expressions (not in exact mode: can create some round-off issues)
		if (!eval.exact()) {
			modulesFile = (ModulesFile) modulesFile.simplify();
		}
		// Get info
		varList = modulesFile.createVarList();
		labelList = modulesFile.getLabelList();
		labelNames = labelList.getLabelNames();
		
		// Create data structures for exploring model
		updater = new Updater<Value>(modulesFile, varList, eval, parent);
		transitionList = new TransitionList<Value>(eval);
		transitionListBuilt = false;
	}
	
	// Methods for ModelInfo interface
	
	@Override
	public ModelType getModelType()
	{
		return modelType;
	}

	@Override
	public void setSomeUndefinedConstants(Values someValues) throws PrismException
	{
		setSomeUndefinedConstants(someValues, false);
	}

	@Override
	public void setSomeUndefinedConstants(Values someValues, boolean exact) throws PrismException
	{
		// We start again with a copy of the original modules file
		// and set the constants in the copy.
		// As {@code initialise()} can replace references to constants
		// with the concrete values in modulesFile, this ensures that we
		// start again at a place where references to constants have not
		// yet been replaced.
		modulesFile = (ModulesFile) originalModulesFile.deepCopy();
		modulesFile.setSomeUndefinedConstants(someValues, exact);
		mfConstants = modulesFile.getConstantValues();
		initialise();
	}
	
	@Override
	public Values getConstantValues()
	{
		return mfConstants;
	}
	
	@Override
	public boolean containsUnboundedVariables()
	{
		return modulesFile.containsUnboundedVariables();
	}
	
	@Override
	public int getNumVars()
	{
		return modulesFile.getNumVars();
	}
	
	@Override
	public List<String> getVarNames()
	{
		return modulesFile.getVarNames();
	}

	@Override
	public List<Type> getVarTypes()
	{
		return modulesFile.getVarTypes();
	}

	@Override
	public DeclarationType getVarDeclarationType(int i) throws PrismException
	{
		return modulesFile.getVarDeclarationType(i);
	}
	
	@Override
	public int getVarModuleIndex(int i)
	{
		return modulesFile.getVarModuleIndex(i);
	}
	
	@Override
	public String getModuleName(int i)
	{
		return modulesFile.getModuleName(i);
	}
	
	@Override
	public VarList createVarList() throws PrismException
	{
		return varList;
	}
	
	@Override
	public int getNumLabels()
	{
		return labelList.size();	
	}

	@Override
	public String getActionStringDescription()
	{
		return "Module/[action]";
	}
	
	@Override
	public List<String> getLabelNames()
	{
		return labelNames;
	}
	
	@Override
	public String getLabelName(int i) throws PrismException
	{
		return labelList.getLabelName(i);
	}
	
	@Override
	public int getLabelIndex(String label)
	{
		return labelList.getLabelIndex(label);
	}
	
	// Methods for ModelGenerator interface
	
	@Override
	public Evaluator<Value> getEvaluator()
	{
		return eval;
	}
	
	@Override
	public boolean hasSingleInitialState() throws PrismException
	{
		return modulesFile.getInitialStates() == null;
	}
	
	@Override
	public State getInitialState() throws PrismException
	{
		if (modulesFile.getInitialStates() == null) {
			return modulesFile.getDefaultInitialState(eval.exact());
		} else {
			// Inefficient but probably won't be called
			return getInitialStates().get(0);
		}
	}
	
	@Override
	public List<State> getInitialStates() throws PrismException
	{
		List<State> initStates = new ArrayList<State>();
		// Easy (normal) case: just one initial state
		if (modulesFile.getInitialStates() == null) {
			State state = modulesFile.getDefaultInitialState(eval.exact());
			initStates.add(state);
		}
		// Otherwise, there may be multiple initial states
		// For now, we handle this is in a very inefficient way
		else {
			Expression init = modulesFile.getInitialStates();
			List<State> allPossStates = varList.getAllStates();
			for (State possState : allPossStates) {
				if (!eval.exact() && init.evaluateBoolean(modulesFile.getConstantValues(), possState)) {
					initStates.add(possState);
				}
				if (eval.exact() && init.evaluateExact(modulesFile.getConstantValues(), possState).toBoolean()) {
					initStates.add(possState);
				}
			}
		}
		return initStates;
	}

	@Override
	public void exploreState(State exploreState) throws PrismException
	{
		this.exploreState = exploreState;
		transitionListBuilt = false;
	}
	
	@Override
	public int getNumChoices() throws PrismException
	{
		return getTransitionList().getNumChoices();
	}

	@Override
	public int getNumTransitions() throws PrismException
	{
		return getTransitionList().getNumTransitions();
	}

	@Override
	public int getNumTransitions(int i) throws PrismException
	{
		return getTransitionList().getChoice(i).size();
	}

	@Override
	public int getChoiceIndexOfTransition(int index) throws PrismException
	{
		return getTransitionList().getChoiceIndexOfTransition(index);
	}
	
	@Override
	public int getChoiceOffsetOfTransition(int index) throws PrismException
	{
		return getTransitionList().getChoiceOffsetOfTransition(index);
	}
	
	@Override
	public int getTotalIndexOfTransition(int i, int offset) throws PrismException
	{
		return getTransitionList().getTotalIndexOfTransition(i, offset);
	}
	
	@Override
	public Object getTransitionAction(int i, int offset) throws PrismException
	{
		TransitionList<Value> transitions = getTransitionList();
		int a = transitions.getTransitionModuleOrActionIndex(transitions.getTotalIndexOfTransition(i, offset));
		return a < 0 ? null : modulesFile.getSynch(a - 1);
	}

	@Override
	public String getTransitionActionString(int i, int offset) throws PrismException
	{
		TransitionList<Value> transitions = getTransitionList();
		int a = transitions.getTransitionModuleOrActionIndex(transitions.getTotalIndexOfTransition(i, offset));
		return getDescriptionForModuleOrActionIndex(a);
	}
	
	@Override
	public Object getChoiceAction(int index) throws PrismException
	{
		TransitionList<Value> transitions = getTransitionList();
		int a = transitions.getChoiceModuleOrActionIndex(index);
		return a < 0 ? null : modulesFile.getSynch(a - 1);
	}

	@Override
	public String getChoiceActionString(int index) throws PrismException
	{
		TransitionList<Value> transitions = getTransitionList();
		int a = transitions.getChoiceModuleOrActionIndex(index);
		return getDescriptionForModuleOrActionIndex(a);
	}

	/**
	 * Utility method to get a description for an action label:
	 * "[a]" for a synchronous action a and "M" for an unlabelled
	 * action belonging to a module M. Takes in an integer index:
	 * -i for independent in ith module, i for synchronous on ith action
	 * (in both cases, modules/actions are 1-indexed) 
	 */ 
	private String getDescriptionForModuleOrActionIndex(int a)
	{
		if (a < 0) {
			return modulesFile.getModuleName(-a - 1);
		} else if (a > 0) {
			return "[" + modulesFile.getSynchs().get(a - 1) + "]";
		} else {
			return "?";
		}
	}
	
	@Override
	public Value getTransitionProbability(int i, int offset) throws PrismException
	{
		TransitionList<Value> transitions = getTransitionList();
		return transitions.getChoice(i).getProbability(offset);
	}

	@Override
	public Value getChoiceProbabilitySum(int i) throws PrismException
	{
		TransitionList<Value> transitions = getTransitionList();
		return transitions.getChoice(i).getProbabilitySum();
	}
	
	@Override
	public Value getProbabilitySum() throws PrismException
	{
		TransitionList<Value> transitions = getTransitionList();
		return transitions.getProbabilitySum();
	}
	
	@Override
	public boolean isDeterministic() throws PrismException
	{
		TransitionList<Value> transitions = getTransitionList();
		return transitions.isDeterministic();
	}
	
	@Override
	public String getTransitionUpdateString(int i, int offset) throws PrismException
	{
		TransitionList<Value> transitions = getTransitionList();
		return transitions.getTransitionUpdateString(transitions.getTotalIndexOfTransition(i, offset), exploreState);
	}
	
	@Override
	public String getTransitionUpdateStringFull(int i, int offset) throws PrismException
	{
		TransitionList<Value> transitions = getTransitionList();
		return transitions.getTransitionUpdateStringFull(transitions.getTotalIndexOfTransition(i, offset));
	}
	
	@Override
	public State computeTransitionTarget(int index, int offset) throws PrismException
	{
		return getTransitionList().getChoice(index).computeTarget(offset, exploreState);
	}

	@Override
	public boolean isLabelTrue(int i) throws PrismException
	{
		Expression expr = labelList.getLabel(i);
		return eval.exact() ? expr.evaluateExact(exploreState).toBoolean() : expr.evaluateBoolean(exploreState);
	}
	
	// Methods for RewardGenerator interface

	@Override
	public List<String> getRewardStructNames()
	{
		return modulesFile.getRewardStructNames();
	}
	
	@Override
	public boolean rewardStructHasStateRewards(int i)
	{
		return modulesFile.rewardStructHasStateRewards(i);
	}
	
	@Override
	public boolean rewardStructHasTransitionRewards(int i)
	{
		return modulesFile.rewardStructHasTransitionRewards(i);
	}
	
	@Override
	public Value getStateReward(int r, State state) throws PrismException
	{
		RewardStruct rewStr = modulesFile.getRewardStruct(r);
		int n = rewStr.getNumItems();
		Value d = eval.zero();
		for (int i = 0; i < n; i++) {
			if (!rewStr.getRewardStructItem(i).isTransitionReward()) {
				Expression guard = rewStr.getStates(i);
				boolean guardSat;
				if (eval.exact()) {
					guardSat = guard.evaluateExact(modulesFile.getConstantValues(), state).toBoolean();
				} else {
					guardSat = guard.evaluateBoolean(modulesFile.getConstantValues(), state);
				}
				if (guardSat) {
					Value rew = eval.evaluate(rewStr.getReward(i), modulesFile.getConstantValues(), state);
					if (!eval.isFinite(rew)) {
						throw new PrismLangException("Reward structure is not finite at state " + state, rewStr.getReward(i));
					}
					d = eval.add(d, rew);
				}
			}
		}
		return d;
	}

	@Override
	public Value getStateActionReward(int r, State state, Object action) throws PrismException
	{
		RewardStruct rewStr = modulesFile.getRewardStruct(r);
		int n = rewStr.getNumItems();
		Value d = eval.zero();
		for (int i = 0; i < n; i++) {
			if (rewStr.getRewardStructItem(i).isTransitionReward()) {
				Expression guard = rewStr.getStates(i);
				String cmdAction = rewStr.getSynch(i);
				if (action == null ? (cmdAction.isEmpty()) : action.equals(cmdAction)) {
					boolean guardSat;
					if (eval.exact()) {
						guardSat = guard.evaluateExact(modulesFile.getConstantValues(), state).toBoolean();
					} else {
						guardSat = guard.evaluateBoolean(modulesFile.getConstantValues(), state);
					}
					if (guardSat) {
						Value rew = eval.evaluate(rewStr.getReward(i), modulesFile.getConstantValues(), state);
						if (!eval.isFinite(rew)) {
							throw new PrismLangException("Reward structure is not finite at state " + state, rewStr.getReward(i));
						}
						d = eval.add(d, rew);
					}
				}
			}
		}
		return d;
	}

	// Local utility methods
	
	/**
	 * Returns the current list of available transitions, generating it first if this has not yet been done.
	 */
	private TransitionList<Value> getTransitionList() throws PrismException
	{
		// Compute the current transition list, if required
		if (!transitionListBuilt) {
			updater.calculateTransitions(exploreState, transitionList);
			transitionListBuilt = true;
		}
		return transitionList;
	}
}
