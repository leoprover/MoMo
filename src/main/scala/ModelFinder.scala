package MoMo

import leo.datastructures.TPTP
import leo.datastructures.TPTP.TFF._

import io.github.cvc5._
import io.github.cvc5.modes._

class ModelFinder(premises: String, inference: String) {
	//maybe add a list for when tptp to smt; list the symbols?
	//what it's supposed to do: accept premises and the inference. try to find (counter-)model
	final def apply(): String = { //probably not as a string but idk what yet
		//check whether unsat was returned
		var satStatus = 0 //1 if unsat
		//to save result/model
		var res = ""

		//set ss to premise + inference
		var ss = "(set-logic UF)\n"
		ss += "(declare-sort $i 0)\n"
		ss += premises + inference
		ss += "(check-sat)\n"
		ss += "(get-model)"

		//create term manager and solver
		val tm = new TermManager()
		val solver = new Solver(tm)

		//print "success" after every successful command, mostly for debugging and stuff
		solver.setOption("print-success", "true")

		// We will ask the solver to produce models and unsat cores,
  		// hence these options should be turned on.
		solver.setOption("produce-models", "true")  
		solver.setOption("finite-model-find", "true")

		//create input parser associated to the solver
		val parser = new InputParser(solver)

		//set ss as parser input
		parser.setStringInput(InputLanguage.SMT_LIB_2_6, ss, "cvc5Stream")
		//create symbol manager to invoke commands here
		val sm = parser.getSymbolManager()

		//initialise object for commands
		var cmd = parser.nextCommand()
	
		//actual commanding
		while (!cmd.isNull() & satStatus == 0) {
			println(s"Executing command ${cmd}: ")
			res = cmd.invoke(solver, sm)
			println(res)
			if (res == "unsat\n") {
				satStatus = 1
			} else {
				cmd = parser.nextCommand()
			}
		}

		return res
	}

}

object ModelFinder {

	final def apply(premises: String, inference: String): String = {
		val modelfinder = new ModelFinder(premises, inference)
		modelfinder.apply()
	}

}
