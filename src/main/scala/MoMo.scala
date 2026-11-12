package MoMo


//import test.ModelFinder._

import leo.datastructures.TPTP
import leo.datastructures.TPTP.TFF._
import leo.modules.input.TPTPParser

import java.io.{FileNotFoundException, File, FileWriter}
import java.nio.file.{InvalidPathException, Path, Paths, Files}

import scala.sys.process._

import scala.concurrent.{Future, Await}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._

import scala.util.{Try, Success, Failure}
import scala.io.StdIn.readLine

//[WIP] general to do: saving models, type inference, recheck errors, cleaning "debugging" println, flexible designation?


object MoMo {
	final val version = "0.1.3"
	
	//variables to store info from cmd line arguments
	private[this] var problemPath : String = ""
	private[this] var timeout : Int = 60
	private[this] var worldNumber : Option[Int] = None
	private[this] var modelPath : Option[String] = None
	private[this] var letPath = Path.of("./lib/logic-embedding-app-1.9.2.jar").toAbsolutePath
	private[this] var modelType = "model"
	private[this] var tmpFile : Option[java.nio.file.Path] = None
 	
	
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
				parseArgs(args.toSeq)
			} catch {
				case ex: NumberFormatException => 
					//println("error during cmd line parsing. " + ex.getMessage)
					printOutput("ERR", None, Some(ex.getClass.toString), Some("error during cmd line parsing. " + ex.getMessage))					
					//System.exit(1)
				case ex: IllegalArgumentException => 
					//println("error during cmd line parsing. " + ex.getMessage) 
					//System.exit(1)
					printOutput("ERR", None, Some(ex.getClass.toString), Some("error during cmd line parsing. " + ex.getMessage))
				case ex: NoSuchElementException =>
					//println("error during cmd line parsing. " + ex.getMessage) 
					//System.exit(1)
					printOutput("ERR", None, Some(ex.getClass.toString), Some("error during cmd line parsing. " + ex.getMessage))
				case ex: Throwable =>
					printOutput("ERR", None, Some(ex.getClass.toString), Some("unexpected error during cmd line parsing. " + ex.getMessage))
			}
		}
		println("Finished parsing cmd line args")
		//[WIP] when upgrading to scala3, LET will be proper dependency, so this will change anyway sometime. making sure that let's error msgs are displayed as well can be done then i guess

		val letCmd = "java -Xss32m -Xmx1g -jar " + letPath.toString + " " + problemPath.toString
		var letProblem = ""
		try {
			letProblem = letCmd.!!
		} catch {
			//case e: java.lang.InterruptedException
			case e : Throwable => {
				//println("error during the embedding of the foml problem to fol")
				//println(e.getClass)
				printOutput("ERR", None, Some(e.getClass.toString), Some("error during the embedding of the foml problem to fol"))
			}
		} finally {

			tmpFile match {
				case None => {
				}
				case Some(tmp: java.nio.file.Path) => {
					Files.delete(tmp)
				}
			}
		}

		
	
		var parsedProblem = TPTPParser.problem(letProblem)
		//println(parsedProblem.pretty)
		println("Finished embedding modal logical problem to classical logic")

		//find out if a model (only axioms) or a countermodel (with conjecture) is searched
		if(parsedProblem.formulas.exists(_.role == "conjecture" )){
			modelType = "countermodel"
		} 

		//extract modal logic definition
		//println("modal logic in use:")
		var modalDef = TPTPParser.annotatedTFF(parsedProblem.formulaComments(parsedProblem.formulas.head.name).filter(com => com.content.contains("tff(")).head.content.replace("%",""))
		//println(modalDef.pretty)

		//[WIP] check if designation is flexible(not supported)
		if(modalDef.pretty.contains("flexible")) {
			printOutput("ERR", None, Some("class java.lang.Throwable"), Some("flexible designation not yet supported"))
		}

		//use classical method for classical model
		////currently only cvc5 => translation to SMT 
		var smtProblem = Seq("")
		try {
			smtProblem = TPTP2SMTTranslator.apply(parsedProblem)
		} catch {
			case ex: Throwable => {
				printOutput("ERR", None, Some(ex.getClass.toString), Some("unexpected error during translation from tptp to smt-lib: " + ex.getMessage))
			}
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
			case e: java.util.concurrent.TimeoutException => {
				//println("model finder timeout")
				//System.exit(1)
				printOutput("TMO", None, Some(e.getClass.toString), Some(e.getMessage))
			}
		}

		//translate model to Kripke-model(TPTP)

		model match {  //eventually handle output generation also via helper function for outputs, handle proper SZS... and stuff!
			case "unsat\n" => {
				//[WIP] Check conjecture+unsat => no countermodel/; no conjecture+unsat => no model/UNS
				modelType match {
					case "model" => {
						printOutput("UNS", None, None, None)
					}
					case "countermodel" => {
						printOutput("THM", None, None, None)
					}
				}
			}
			case "unknown\n" => {
				printOutput("GUP", None, None, None)
			}
			case _ => {//[WIP] error handling (error from unexpected fol model finder output OR error within translation process)
				//println("finite model found (smt)")
				//println(model)
				try {
					val kripkeModel = FOL2FOMLModelTranslator.apply(modalDef, model, "smt")
					//kripkeModel.printModel()
					modelType match {
						case "model" => {
							printOutput("SAT", Some(kripkeModel), None, None)
						}
						case "countermodel" => {
							printOutput("CSA", Some(kripkeModel), None, None)
						}
					}
				} catch {
					case ex: Throwable => {
						//println("unexpected error during translation of the generated fol model to a kripke model: " + ex.getMessage)
						printOutput("ERR", None, Some(ex.getClass.toString), Some("unexpected error during translation of the generated fol model to a kripke model: " + ex.getMessage))
					}
				}
			}
		}
		
	}

	//method to print the help stuff when evoking on cmd line
	private[this] final def printHelp(): Unit = {
		print("Usage: MoMo <problem> [options]\n MoMo is a finite model finder for first-order modal logics in TPTP problem format NXF.\n In case the given problem includes a conjecture, a countermodel is searched. Otherwise a model satisfying the given axioms is searched.\n If a (counter-)model is found, it is given in stdout.\n\n Parameters:\n <problem> :	Either contains the file path of the problem file as a String OR (planned:) is '-' to input problem via stdin\n\n Options:\n --help | -h	view usage, including necessary parameters and options.\n --timeout | -t	set a time limit for timeouts in seconds. Default value: 60sec.\n --saveModel | -s	give path to a file where a generated model will be saved in. If the file already exists, the file will be overwritten.\n --worlds | -w	set the number of worlds that the generated model has to include exactly. The number has to be an integer > 0")
	}

	//method to parse cmd line arguments
	private[this] final def parseArgs(args: Seq[String]): Unit = {
		problemPath = args.head
		//[WIP] read in problem from stdin
		if (!Files.exists(Paths.get(problemPath)) & problemPath != "-") {
			throw new InvalidPathException("No such file exists.", problemPath)
		}

		if(problemPath == "-"){ //read input from std in
			var  r = ""
			var f = ""
			println("Input the problem via std input, one annotated formula (or tptp comment) per line. end input with '%END%':")
			while(r != "%END%"){
				r = readLine()
				if(r != "%END%") {
					try{
						if(r.head.toString != "%"){
							TPTPParser.annotatedTFF(r)
						}
						f += r + "\n"
					} catch {
						case e: Throwable => {
							println("% invalid tptp annotated formula: " + e.getMessage + ". previous annotated formulas are stored, continue input:")
						}
					}
				}
			}
			//println("Input:\n" + f)

			tmpFile = Some(Files.createTempFile(null, ".txt")) //
	 		//println(s"Temp file name: ${tmpFile.toString}")
			//tmpFileS = Some(tmpFile.toString)
			tmpFile match {
				case Some(tmp: java.nio.file.Path) => {
					println(tmp.getClass)
					problemPath = tmp.toString

					val writer = new FileWriter(tmp.toFile)
					writer.write(f)
					writer.close()
				}
				case None => {
					printOutput("ERR", None, None, None)
				}
			}



			//Files.delete(tmpFile)

			//println("From file:")
			//val source = scala.io.Source.fromFile(tmpFile.toFile)
			//val lines = try source.mkString finally source.close()
			//println(lines)

			
			//System.exit(0)
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
									throw new IllegalArgumentException("for input string: " + timeout.toString + "\ninvalid input for timeout. timeout has to be a positive integer.")
								}
								argsO = argsO.tail.tail
								//println(argsO)
							} catch {
								case ex: NumberFormatException => {
									throw new NumberFormatException(ex.getMessage + "\ninvalid input for timeout. timeout has to be a positive integer.")
								}
								case ex: NoSuchElementException => {
									throw new NoSuchElementException("no time limit was given. set the time limit for the timeout to n > 0 via -t n or --timeout n")
								}
								case ex: IllegalArgumentException => {
									throw new IllegalArgumentException(ex.getMessage)
								}
								case ex : Throwable => {
									println(ex.getClass)
									throw new Throwable("argument for timeout")
								}
							}
							println(s"Set timeout to ${timeout}")
						case ("--saveModel" | "-s") =>
							modelPath = Some(argsO.tail.head)
							modelPath match {
								case None => {
								}
								case Some(path: String) => {
									println(s"If a model is found, it will be saved in $path")
									if (Files.exists(Paths.get(path))) {
										println("Path where model will be saved exists already. The file will be overwritten.")	
									}
								}
							}
							argsO = argsO.tail.tail
						case ("--worlds" | "-w") =>
							Try{argsO.tail.head.toInt} match {
								case Success(n: Int) => {
									if(n == 0){
										throw new IllegalArgumentException("invalid input for number of worlds. Input needs to be an integer > 0!")
									} else {
										println("specify number of worlds success")
										worldNumber = Some(argsO.tail.head.toInt)
									}
								}
								//case None => {
								case Failure(e) => {
									e match {
										case error: NumberFormatException => {
											throw new NumberFormatException(e.getMessage + "\ninvalid input for number of worlds. input needs to be an integer > 0!")
										}
										case error: NoSuchElementException => {
											throw new NoSuchElementException("no number of worlds was specified. set the number of worlds to n > 0 via -w n or --worlds n")
										}
									}
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

	def printOutput(szs: String, model: Option[KripkeModel], errorClass: Option[String], errorMessage: Option[String]): Unit = {
		szs match {
			//successes
			case "SAT" => {
				println("% SZS status Satisfiable")
				println("% SZS output start FiniteModel")
				model match {
					case Some(k: KripkeModel) => {
						k.printModel()

						println("% SZS output end FiniteModel")

						modelPath match {
							case None => {
								//println("% no model is saved")
							}
							case Some(path: String) => {
								val writer = new FileWriter(Paths.get(path).toFile)
								writer.write(k.pretty)
								writer.close()
								println("% saved model to " + path)
							}
						}
					}
					case None => {
					}
				}
			}
			case "CSA" => {
				println("% SZS status CounterSatisfiable")
				println("% SZS output start FiniteModel")
				model match {
					case Some(k: KripkeModel) => {
						k.printModel()
						println("% SZS output end FiniteModel")

						modelPath match {
							case None => {
								//println("% no model is saved")
							}
							case Some(path: String) => {
								val writer = new FileWriter(Paths.get(path).toFile)
								writer.write(k.pretty)
								writer.close()
								println("% saved model to " + path)
							}
						}

					}
					case None => {
					}
				}
				//println("% SZS output end FiniteModel")
			}

			case "UNS" => {
				println("% SZS status Unsatisfiable")
			}
			case "THM" => {
				println("% SZS status Theorem: no countermodel was found.")
			}

			//failures
			case "TMO" => {
				errorClass match {
					case Some(c: String) => {
						print("% SZS status Timeout: " + c)
						errorMessage match {
							case Some(m: String) => {
								println(m)
							}
							case None => {
								print("\n")
							}
						}
					}
					case None => {
						print("% SZS status Timeout")
					}
				}
				System.exit(1)
			}
			case "GUP" => {
				println("% SZS status GaveUp")
				//print(error.getMessage)
				System.exit(1)
			}
			case "ERR" => {
				errorClass match {
					case Some(c: String) => {
						print("% SZS status Error: " + c)
						errorMessage match {
							case Some(m: String) => {
								println(": " + m)
							}
							case None => {
								print("\n")
							}
						}
					}
					case None => {
						print("% SZS status Error")
					}
				}
				System.exit(1)
			}
		}
	}

}