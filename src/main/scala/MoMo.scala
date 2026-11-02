package MoMo


//import test.ModelFinder._

import leo.datastructures.TPTP
import leo.datastructures.TPTP.TFF._
import leo.modules.input.TPTPParser

import java.io.FileNotFoundException
import java.nio.file.{InvalidPathException, Path, Paths, Files}

import scala.sys.process._

import scala.concurrent.{Future, Await}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._

import scala.util.{Try, Success, Failure}


object MoMo {
	final val version = "0.1.3"
	
	//variables to store info from cmd line arguments
	private[this] var problemPath : String = ""
	private[this] var timeout : Int = 60
	private[this] var worldNumber : Option[Int] = None
	private[this] var modelPath : String = "" //or rather Option? probably
	private[this] var letPath = Path.of("./lib/logic-embedding-app-1.9.2.jar").toAbsolutePath
	
	//main process
	final def main(args: Array[String]): Unit = {
		//parse cmd line arguments
		if (args.contains("--help") | args.contains("-h")) {
			printHelp()
			return
		}
		if (args.contains("--version") | args.contains("-v")) {
			println(s"$version")
			return
		}
		if (args.length == 0) { 
			printHelp()
			println("\nPlease, include necessary parameters and, if needed, options!")
			return
		} else {
			try {
//[WIP] proper error handling: errors should be thrown inside parseArgs so that catch can actually... catch them(?), instead of handling them all inside the function i guess?
				parseArgs(args.toSeq)
			} catch {
				case ex: NumberFormatException => 
					//println("numberformat")
					println(ex.getMessage)
					System.exit(1)
				case ex: IllegalArgumentException => 
					//println("illegal")
					println(ex.getMessage) 
					System.exit(1)
				case ex: Throwable =>
					println("unexpected error during parsing " + ex.getMessage + ".\n See the help information for possible arguments and options:\n")
					printHelp()
					System.exit(1)
			}
		}
		println("Finished parsing cmd line args")
		//[WIP] when upgrading to scala3, LET will be proper dependency, so this will change anyway sometime. making sure that let's error msgs are displayed as well can be done then i guess
		val letCmd = "java -jar " + letPath.toString + " " + problemPath.toString
		var letProblem = ""
		try {
			letProblem = letCmd.!!
		} catch {
			case _ : Throwable => {
				println("error: sth wrong with tptp problem :(")
				System.exit(1)
			}
		}
	
		var parsedProblem = TPTPParser.problem(letProblem)
		//println(parsedProblem.pretty)
		println("Finished embedding modal logical problem to classical logic")
		//extract modal logic definition
		//println("modal logic in use:")
		var modalDef = TPTPParser.annotatedTFF(parsedProblem.formulaComments(parsedProblem.formulas.head.name).filter(com => com.content.contains("tff(")).head.content.replace("%",""))
		//println(modalDef.pretty)

		//[WIP] check if designation is flexible(not supported)

		//use classical method for classical model
		////currently only cvc5 => translation to SMT 
		var smtProblem = Seq("")
		try {
			smtProblem = TPTP2SMTTranslator.apply(parsedProblem)
		} catch {
			case _ => println("unexpected error during translation to smt-lib") //[WIP] error and end process
		}
		println("Finished translation to smt-lib")

		////hand over to cvc5

		val finding = Future { //for timing out cvc5 bc it doesn't have built-in timeout as an API
			findModel(smtProblem)
		}

		var model = ""

		try {
			model = Await.result(finding, timeout.second)
		} catch {
			case _: java.util.concurrent.TimeoutException => {
				println("model finder timeout")
				System.exit(1)
			}
		}

		//translate model to Kripke-model(TPTP)

		model match {  //eventually handle output generation also via helper function for outputs, handle proper SZS... and stuff!
			case "unsat\n" => {
				//[WIP] Check conjecture+unsat => no countermodel/; no conjecture+unsat => no model/UNS
				println("no finite countermodel")
			}
			case "unknwon\n" => {
				//[WIP] proper give up SZS
				println("model finder gave up")
			}
			case _ => {//[WIP] error handling (error from unexpected fol model finder output OR error within translation process)
				//[WIP] print output model + SZS: conjecture+model => countermodel/CSA; no conjecture+model => model/SAT
				println("finite model found (smt)")
				println(model)
				FOL2FOMLModelTranslator.apply(modalDef, model, "smt")
			}
		}
		
	}

	//method to print the help stuff when evoking on cmd line
	private[this] final def printHelp(): Unit = {
		print("Usage: MoMo <problem> [options]\n MoMo is a finite model finder for first-order modal logics in TPTP problem format NXF.\n In case the given problem includes a conjecture, a countermodel is searched. Otherwise a model satisfying the given axioms is searched.\n If a (counter-)model is found, it is given in stdout.\n\n Parameters:\n <problem> :	Either contains the file path of the problem file as a String OR (planned:) is '-' to input problem via stdin\n\n Options:\n --help | -h	view usage, including necessary parameters and options.\n --timeout | -t	set a time limit for timeouts. Default value: 60sec.\n ")
	}

	//method to parse cmd line arguments
	private[this] final def parseArgs(args: Seq[String]): Unit = {
		problemPath = args.head
		//[WIP] read in problem from stdin
		if (!Files.exists(Paths.get(problemPath))) {
			throw new InvalidPathException("No such file exists.", problemPath)
		}

		var argsO = args.tail
		if(argsO.nonEmpty){
			var arg = argsO.head
			while (!arg.equals("")) {
				//println(arg)
				if (!arg.head.toString.equals("-")) {
					throw new IllegalArgumentException("Superfluous parameters supplied")
				} else {
					arg match {
						case ("--timeout" | "-t") =>
							try{
								timeout = argsO.tail.head.toInt
								if(timeout < 1){
									throw new NumberFormatException("For input string: " + timeout.toString)
								}
								argsO = argsO.tail.tail
								//println(argsO)
							} catch {
								case ex: NumberFormatException => 
									//println("Invalid input for timeout. Timeout has to be a integer.")
									throw new NumberFormatException(ex.getMessage + ": Invalid input for timeout. Timeout has to be a positive integer.")
								case _ : Throwable =>
									throw new Throwable("argument for timeout ")
							}
							println(s"Set timeout to ${timeout}")
						case ("--saveModel" | "-s") =>
							//[WIP] check if modelPath exists before
							modelPath = argsO.tail.head
							argsO = argsO.tail.tail
							println(s"If a model is found, it will be saved in $modelPath")
							//println(argsO)
						case ("--worlds" | "-w") =>
							//try{
							//	worldNumber = argsO.tail.head.toInt
							//	argsO = argsO.tail.tail
								//println(argsO)
							//} catch {
							//	case ex: NumberFormatException => {
							//		println("No number of worlds is specified.")
							//		System.exit(1)
							//	}
							//	case _ : Throwable =>
							//		println("No number of worlds is specified.")
							//		System.exit(1)
							//}
							//worldNumber = Some(argsO.tail.head.toInt)
							//if(worldNumber == None | worldNumber == Some(0)) {
							//	throw new NumberFormatException("invalid input for number of worlds. Input needs to be an integer > 0!")
							//}
							
							Try{argsO.tail.head.toInt} match {
								case Success(n: Int) => {
									if(n == 0){
										throw new NumberFormatException("invalid input for number of worlds. Input needs to be an integer > 0!")
									} else {
										println("specify number of worlds success")
										worldNumber = Some(argsO.tail.head.toInt)
									}
								}
								//case None => {
								case Failure(e) => {
									throw new NumberFormatException(e.getMessage + "\nInvalid input for number of worlds. Input needs to be an integer > 0!")
								}
							}
							argsO = argsO.tail.tail

						case _ =>
							throw new IllegalArgumentException("Invalid options given. To view all valid options, use --help or -h.")
							//argsO = argsO.tail
							//println(argsO)
					}
				}
				if (argsO.nonEmpty) {
					arg = argsO.head
				} else {
					arg = ""
				}
			}
		}
	}

	private def findModel(smtProblem: Seq[String]): String = {
		var model = ""

		worldNumber match {
			case Some(wn: Int) => { //adds additional formulas to fix number of worlds model is supposed to have
				if(wn > 1){
					var worldConstraint = "(assert (forall ("
					for(n <- Seq.range(0, wn + 1)){
						worldConstraint += "(W" + n.toString + " $world) "
					}
					worldConstraint = worldConstraint.dropRight(1) + ") (=> (and "
					for(n <- Seq.range(0, wn - 1)){
						//[WIP] needs some cleaning of prints
						print("#############")
						println(n.toString)
						println(wn)
						println("compare with")
						for(m <- Seq.range(n+1, wn)){   
							println(m)
							worldConstraint += "(not (= W" + n.toString + " W" + m.toString + ")) "
						}
					}
					worldConstraint = worldConstraint.dropRight(1) + ") (or "
					for(n <- Seq.range(0, wn)){
						worldConstraint += "(= W" + wn.toString + " W" + n.toString + ") "
					}
					worldConstraint = worldConstraint.dropRight(1) + "))))\n"
	
					worldConstraint += "(assert (exists ("
					for(n <- Seq.range(0, wn)){
						worldConstraint += "(W" + n.toString + " $world) "
					}
					if(wn > 2) {
						worldConstraint = worldConstraint.dropRight(1) + ") (and "
						for(n <- Seq.range(0, wn - 1)){
							print("#############")
							println(n.toString)
							println(wn)
							println("compare with")
							for(m <- Seq.range(n+1, wn)){
								println(m)
								worldConstraint += "(not (= W" + m.toString + " W" + n.toString + ")) "
							}
						}
						worldConstraint = worldConstraint.dropRight(1) + ")))"
					} else {//wn == 2
						worldConstraint = worldConstraint.dropRight(1) + ") (not (= W1 W0))))"
					}
			
					println(worldConstraint)
					model = ModelFinder.apply(smtProblem(0) + smtProblem(1) + worldConstraint, smtProblem(2))
				} else { //wn == 1, as wn == 0 excluded during cmd line arg parsing
					model = ModelFinder.apply(smtProblem(0) + smtProblem(1) + "(assert (forall ((W0 $world) (W1 $world)) (not (= W0 W1))))", smtProblem(2))
				}
			}
			case None => {
				model = ModelFinder.apply(smtProblem(0) + smtProblem(1), smtProblem(2))
			}
		}

		return model

	}

}