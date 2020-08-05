package prism;

import java.io.File;
import java.io.FileNotFoundException;

import parser.State;
import parser.ast.Expression;
import parser.ast.FormulaList;
import parser.ast.ModulesFile;

public class AbstractionTest
{

	public static void main(String[] args)
	{
		new AbstractionTest().run(args);
	}

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
			// (just a single one for now)
			String abstractVar = null;
			Expression abstractVarExpr = null;
			FormulaList formulaList = modulesFile.getFormulaList();
			for (int i = 0; i < formulaList.size(); i++) {
				String formulaName = formulaList.getFormulaName(i);
				if (formulaName.startsWith("abs_")) {
					abstractVar = formulaName.substring(4);
					abstractVarExpr = formulaList.getFormula(i);
					System.out.println(abstractVar + " : " + abstractVarExpr);
				}
			}
			
			// Get model generator for PRISM model
			prism.loadPRISMModel(modulesFile);
			ModelGenerator<?> modelGen = prism.getModelGenerator();
			
			// Examine initial state
			State state = modelGen.getInitialState();
			System.out.println("Initial state: " + state);
			System.out.println("Abstract variable value: " + abstractVarExpr.evaluate(state));
			
			// Examine successor states
			modelGen.exploreState(state);
			int numTransitions = modelGen.getNumTransitions(0);
			for (int i = 0; i < numTransitions; i++) {
				state = modelGen.computeTransitionTarget(0, i);
				System.out.println("Successor state: " + state);
				System.out.println("Abstract variable value: " + abstractVarExpr.evaluate(state));
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

}
