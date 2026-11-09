package MoMo

import leo.datastructures.TPTP
import leo.datastructures.TPTP.AnnotatedFormula
import leo.datastructures.TPTP.TFF._
import leo.modules.input.TPTPParser

import scala.collection.mutable.Map
import scala.collection.mutable.Stack

//think abt restructuring it: more helper structuring. esp. for interpretations, helper structure is... convoluted? 
final class FOL2FOMLModelTranslator(modalDef: AnnotatedFormula, model: Seq[String]) {
	def smt(): Unit = {//KripkeModel {
		//intermediate helper structures. symbols should be saved in the form they may be used in TPTP format
		//println("go into fol(smt)2foml translator success")
		var sorts: Option[scala.collection.mutable.Map[String, Stack[String]]] = None //[WIP] can reformulate to not make it option bc sort incl $world always. unless i allow classical fol, too?
		if( model.exists(s => s.startsWith("; cardinality of")) ){
			sorts = Some(Map.empty[String, Stack[String]])
		}
		var opName: scala.collection.mutable.Map[String, Seq[String]] = Map.empty[String, Seq[String]]
		var opInterp: scala.collection.mutable.Map[String, Map[String, Seq[String]]] = Map.empty[String, Map[String, Seq[String]]]

		//extract nec info from found fol model
		for(line <- model){
			line match{
				////note sort symbols (incl. the one for worlds)
				case card if card.startsWith("; cardinality of") => {
					sorts match{
						case Some(sortsMap: Map[String, Stack[String]]) => {
							var sortName = card.split(" ")(3)
							sortsMap.update(sortName, Stack.empty[String])
							sorts = Some(sortsMap)
						}
						case None => {
							throw new Throwable("no sorts (incl. one for worlds) in fol model")
						}
					}
				}
				////note symbols for worlds/domain elements
				case dElement if dElement.startsWith("; rep: ") => {
					val sortName = dElement.split(" ")(4).replace(")","")
					sorts match{
						case Some(sortsMap: Map[String, Stack[String]]) => {
							sortsMap.get(sortName) match {
								case Some(domain: Stack[String]) => {
									domain.push(dElement.split(" ")(3).replace("@","").replace("$",""))
								}
								case None => {
									throw new Throwable("for sort" + sortName + "fol domain is found to be empty.")
								}
							}
						}
						case None => {
							throw new Throwable("no sorts (incl. one for worlds) in fol model")
						}
					}
				}
				////extract info about predicate/propositional/function/constant (operational) symbols
				case interp if interp.startsWith("(define-fun") => {
					var interpH = interp.replace(")(", ") (").split(" ").tail
					var opNameNow = interpH.head //operational symbol that is worked on now
					opName.update(opNameNow, Seq.empty[String])
					opInterp.update(opNameNow, Map.empty[String, Seq[String]])
					interpH = interpH.tail
					var in = Map.empty[Int, String] //variables used to define the symbol's interpretation and which argument they rep
					var inType = Map.empty[Int, String] //the sorts of the arguments
					var out = "" //output sort
					if(interpH.head.replace("(","").replace(")","").replace(" ","") != ""){
						//////note info abt argument and output of op
						while(out == "") {
							interpH.head match {
								case name if name.contains("(") => {
									//println(name)
									in.update(in.size, name.replace("(","").replace(")",""))
								}
								case sort if sort.contains(")") => {
									//println(sort)
									inType.update(inType.size, sort.replace("(","").replace(")",""))
								}
								case _ => {
									out = interpH.head.replace("Bool", "$o")
								}
							}
							interpH = interpH.tail
						}
					} else { //op is constant or propositional symbol
						interpH = interpH.tail
						out = interpH.head.replace("Bool", "$o")
						interpH = interpH.tail
					}

					interpH = interpH.mkString(" ").dropRight(1).split(" ")

					////////note sorts of output/input. format: (output sort, input sort 1, ..., input sort n)
					opName(opNameNow) = Seq(out)
					for(n <- 0 until inType.size){
						opName(opNameNow) = opName(opNameNow).concat(Seq(inType(n)))
					}

					println(opName)
					//////note interpretation in each world
					var opStack = Stack.empty[String]
					if(opName(opNameNow).head == "$o"){ //for propositional/predicate symbols
						sorts match {
							case Some(sortsMap: Map[String, Stack[String]]) => {
								if(opNameNow.equals("$accessible_world")){ //specifically for $accessible_world [WIP] maybe this can be shortened and further merged with gen case?
									interpH.head match {
										case t if t.equals("true") => { //always true
											opInterp.apply(opNameNow).update("default", Seq("$true"))
										}
										case t if t.equals("false") => { //always false
											opInterp.apply(opNameNow).update("default", Seq("$false"))
										}
										case _ => { //otherwise
											opInterp.apply(opNameNow).update("default", Seq("$false"))
											var inNow = Map.empty[String, String]
											var inH = ""
											for(part <- interpH){
												if(part.startsWith("(")){ //new operational status
													opStack.push(part.replace("(",""))
													if(opStack.top == "not"){
														opInterp.apply(opNameNow).update("default", Seq("$true"))
													}
												} else { //different commands based on stack status
													opStack.top match {
														case "as" => {
															if( inH == ""){
																inH = part.replace("@","").replace("$","").replace(")", "")
															} else {
																println(inH)
															}
														}
														case "=" => {
															inNow.update(part.replace(")",""), inH)
															inH = ""
														}
														case "and" => { //may be redundant
															if(in.size == inNow.size){
																inNow =	Map.empty[String, String]
															}
														}
														//case "or" => {
														//}
														case _ => {
															//println("other smt logic op") //error now but may need to be extended for other smt solvers
															throw new Throwable("smt (logic) operation " + opStack.top + " not (yet) supported during model translation.")
														}
													}
													if( part.contains(")")){ //change status by removing op stack tops
														opStack.pop
														if(in.size == inNow.size){
															var h = Seq.empty[String]
															for(n <- in.keys){
																h = h.concat(Seq(inNow.apply(in.apply(n))))
															}
															opInterp.apply(opNameNow).update("all", h)
															inNow =	Map.empty[String, String]
														}
													}
												}
											}
										}
									}
								} else {
									interpH.head match {
										case t if t.equals("true") => { //always true
											opInterp.apply(opNameNow).update("default", Seq("$true"))
										}
										case t if t.equals("false") => { //always false
											if(opNameNow.contains("$exists_in_world_")){
												throw new Throwable(opNameNow + "defines the domain to be empty in each world.")
											} else {
												opInterp.apply(opNameNow).update("default", Seq("$false"))
											}
										}
										case _ => { //otherwise
											opInterp.apply(opNameNow).update("default", Seq("$false"))
											var inNow = Map.empty[String, String]
											var inH = ""
											for(part <- interpH){
												if(part.startsWith("(")){ //update op stack with new status/operation
													opStack.push(part.replace("(",""))
													if(opStack.top == "not"){
														opInterp.apply(opNameNow).update("default", Seq("$true"))
													}
												} else {
													opStack.top match {
														case "as" => {
															if( inH == ""){
																inH = part.replace("@","").replace("$","").replace(")", "")
																
															}
														}
														case "=" => {
															inNow.update(part.replace(")",""), inH)
															inH = ""
														}
														case "and" => { //may be redundant
															if(in.size == inNow.size){
																inNow =	Map.empty[String, String]
															}
														}
														//case "or" => { //currently redundant
														//}
														case _ => {
															//println("other smt logic op") //[WIP] later error
															throw new Throwable("smt (logic) operation " + opStack.top + " not (yet) supported during model translation.") //error now but may need to be extended for other smt solvers
														}
													}
													
													if( part.contains(")")){ //update status by removing top of stack
														opStack.pop
														println("Stacktop: " + opStack.top)
														if(in.size == inNow.size){
															var h = Seq.empty[String]
															for(n <- in.keys){
																h = h.concat(Seq(inNow.apply(in.apply(n))))
															}
															opInterp.apply(opNameNow).update(h.head, h.tail)
															inNow =	Map.empty[String, String]
														}
													}
												}
											}
										}
									}
								}
							}
							case None => {
								throw new Throwable("no sorts (incl. one for worlds) in fol model")
							}
						}
					} else { //constants and functions
						sorts match {
							case Some(sortsMap: Map[String, Stack[String]]) => {
								if((interpH.head.replace("(","").equals("as") & interpH.size == 3) | (opName(opNameNow).size == 1)) { //all mapped to the same elem or simply a constant
									println("function of arity" + opName(opNameNow).size.toString + " or constant")
									println(interpH)
									opInterp.update(opNameNow, Map("default" -> Seq(interpH(1).replace("@", "").replace("$", "")), "all" -> Seq(interpH(1).replace("@", "").replace("$", ""))))
								} else { //[WIP] HEREHEREHERE function with positive arity
									println("function of arity " + (opName(opNameNow).size-1).toString)
									println(interpH.mkString(" "))

									if(modalDef.pretty.contains("flexible")){ //later when flexible designation for functions and constants supported and needed to differentiate
										throw new Throwable("flexible designation not yet supported")
									} else {
										opInterp.apply(opNameNow).update("default", Seq("ite"))
										opInterp.apply(opNameNow).update("all", Seq.empty[String])
										if(interpH.head.contains("ite")) {
											opInterp.apply(opNameNow)("all") = opInterp.apply(opNameNow).apply("all").concat(smtIte(interpH, in))									
										} 
									}	
								}
							}
							case None => {
								throw new Throwable("no sorts (incl. one for worlds) in fol model")
							}
						}
					}
				}
				case _ => {
					throw new Exception("unexpected fol model structure in smt format")
				}
			}
		}
		val kripkemodel = KripkeModel.apply(modalDef, sorts, opName, opInterp)
		kripkemodel.printModel() //[WIP] delete when output function in MoMo finished -> printing model and stuff there
	}

	def smtIte(smtI: Seq[String], in: Map[Int, String]): Seq[String] = {
		println("smtIte")
		var interpH = Seq.empty[String] // "== opInterp.apply(opNameNow).apply("all")"
		var iteStack = Stack.empty[Int]
		var opStack = Stack("")
		var inNow = Map.empty[String, String]
		var inH = ""
		for(part <- smtI){
			println("PART: " + part)
			if(part.startsWith("(")){ 
				if(part.replace("(","") == "ite"){
					interpH  = interpH.concat(Seq("ite"))
					iteStack.push(1)
				}
				opStack.push(part.replace("(",""))
				println("Stack: " + opStack)
			} else {  //different commands based on stack status
				opStack.top match {
					case "as" => {
						if( inH == ""){
							inH = part.replace("@","").replace("$","").replace(")", "")
						} else {
							println(inH)
						}
					}
					case "=" => {
						inNow.update(part.replace(")",""), inH)
						inH = ""
					}
					case _ => {
						//println("other smt logic op") //error now but may need to be extended for other smt solvers
						throw new Throwable("smt (logic) operation " + opStack.top + " not (yet) supported during model translation (functions).")
					}
				}
				var parth = part
				while( parth.contains(")")){ //change status by removing op stack tops
					opStack.pop
					parth = parth.dropRight(1)
					if(opStack.top == "ite"){
						if(inNow.nonEmpty){
							var h = ""
							for(now <- inNow.keys){
								//println(in.filter(_._2 == now).keys.head)
								h += in.filter(_._2 == now).keys.head + "@" + inNow(now) + " "
								println(h)
							}
							h = h.dropRight(1)
							interpH = interpH.concat(Seq(h))
						} else {
							interpH = interpH.concat(Seq(inH))
							inH = ""
						}
						inNow =	Map.empty[String, String]
						var itePop = iteStack.pop
						iteStack.push(itePop + 1)
					}
				}

			}
		}
		println("FINAL: " + interpH.mkString(";"))
		return interpH

	}
	
}



object FOL2FOMLModelTranslator {
	def apply(modalDef: AnnotatedFormula, model: String, format: String): Unit = { //KripkeModel {
		var modelH = model.split("\n").toSeq
		modelH = modelH.slice(1,modelH.size-1)
		val modeltranslator = new FOL2FOMLModelTranslator(modalDef, modelH)
		format match {
			case "smt" => {
				modeltranslator.smt()
			}
			case _ => {
				throw new Throwable("unknown fol model format during translation from fol to foml")
			}
		}
		
	}

}