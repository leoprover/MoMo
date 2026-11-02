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
		println("go into fol(smt)2foml translator success")
		var sorts: Option[scala.collection.mutable.Map[String, Stack[String]]] = None //[WIP] can reformulate to not make it option bc sort incl $world always. unless i allow classical fol, too?
		if( model.exists(s => s.startsWith("; cardinality of")) ){
			sorts = Some(Map.empty[String, Stack[String]])
		}
		var opName: scala.collection.mutable.Map[String, Seq[String]] = Map.empty[String, Seq[String]]
		var opInterp: scala.collection.mutable.Map[String, Map[String, Seq[String]]] = Map.empty[String, Map[String, Seq[String]]]
		for(line <- model){
			println(sorts)
			line match{
				case card if card.startsWith("; cardinality of") => {
					sorts match{
						case Some(sortsMap: Map[String, Stack[String]]) => {
							var sortName = card.split(" ")(3)
							println(sortName)
							sortsMap.update(sortName, Stack.empty[String])
							//println(cardMap)
							sorts = Some(sortsMap)
						}
						case None => {
							println("no sorts") //[WIP] $world is always in sorts
						}
					}
				}
				case dElement if dElement.startsWith("; rep: ") => {
					val sortName = dElement.split(" ")(4).replace(")","")
					sorts match{
						case Some(sortsMap: Map[String, Stack[String]]) => {
							sortsMap.get(sortName) match {
								case Some(domain: Stack[String]) => {
									domain.push(dElement.split(" ")(3).replace("@","").replace("$",""))
								}
								case None => {
									println("no stack") //[WIP] $world is always in sorts
								}
							}
						}
						case None => {
							println("no sorts")
						}
					}
				}
				case interp if interp.startsWith("(define-fun") => {
					var interpH = interp.replace(")(", ") (").split(" ").tail
					var opNameNow = interpH.head
					opName.update(opNameNow, Seq.empty[String])
					opInterp.update(opNameNow, Map.empty[String, Seq[String]])
					println(opName)
					interpH = interpH.tail
					var in = Map.empty[Int, String]
					var inType = Map.empty[Int, String]
					var out = ""
					if(interpH.head.replace("(","").replace(")","").replace(" ","") != ""){
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
							//println(in)
							//println(inType)
							interpH = interpH.tail
						}
					} else {
						interpH = interpH.tail
						out = interpH.head.replace("Bool", "$o")
						interpH = interpH.tail
					}
					println(out)
					println(interpH.mkString(" ").dropRight(1))
					interpH = interpH.mkString(" ").dropRight(1).split(" ")

					//note sorts of output/input
					opName(opNameNow) = Seq(out)
					for(n <- 0 until inType.size){
						opName(opNameNow) = opName(opNameNow).concat(Seq(inType(n)))
					}

					println(opName)
					//note interpretation in each world
					var opStack = Stack.empty[String]
					if(opName(opNameNow).head == "$o"){
						sorts match {
							case Some(sortsMap: Map[String, Stack[String]]) => {
								if(opNameNow.equals("$accessible_world")){
									interpH.head match {
										case t if t.equals("true") => {
											opInterp.apply(opNameNow).update("default", Seq("$true"))
										}
										case t if t.equals("false") => {
											opInterp.apply(opNameNow).update("default", Seq("$false"))
											//[WIP] check if opNameNow is $exists_in_world_X -> shouldn't since then domains are empty: error
										}
										case _ => {
											opInterp.apply(opNameNow).update("default", Seq("$false"))
											var inNow = Map.empty[String, String]
											var inH = ""
											for(part <- interpH){
												if(part.startsWith("(")){
													opStack.push(part.replace("(",""))
													if(opStack.top == "not"){
														opInterp.apply(opNameNow).update("default", Seq("$true"))
													}
												} else {
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
																//println("SAME SIZE")
																inNow =	Map.empty[String, String]
															}
														}
														//case "or" => {
														//}
														case _ => {
															println("other smt logic op") //[WIP] later error
														}
													}
													println(part)
													println(part.filter(_ == ')').size)
													if( part.contains(")")){
														opStack.pop
														println("Stacktop: " + opStack.top)
														if(in.size == inNow.size){
															//println("SAME SIZE")
															var h = Seq.empty[String]
															for(n <- in.keys){
																h = h.concat(Seq(inNow.apply(in.apply(n))))
																//println(inNow.apply(in.apply(n)))
															}
															opInterp.apply(opNameNow).update("all", h)
															inNow =	Map.empty[String, String]
															//println(opInterp)
														}
													}
												}
											}
										}
									}
								} else {
									interpH.head match {
										case t if t.equals("true") => {
											opInterp.apply(opNameNow).update("default", Seq("$true"))
										}
										case t if t.equals("false") => {
											opInterp.apply(opNameNow).update("default", Seq("$false"))
										}
										case _ => {
											opInterp.apply(opNameNow).update("default", Seq("$false"))
											var inNow = Map.empty[String, String]
											var inH = ""
											for(part <- interpH){
												if(part.startsWith("(")){
													opStack.push(part.replace("(",""))
													if(opStack.top == "not"){
														opInterp.apply(opNameNow).update("default", Seq("$true"))
													}
													println("Stacktop: " + opStack.top)
												} else {
													println(part)
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
															print("NOW: ")
															println(inNow)
														}
														case "and" => { //may be redundant
															if(in.size == inNow.size){
																//println("SAME SIZE")
																inNow =	Map.empty[String, String]
															}
														}
														//case "or" => {
														//}
														case _ => {
															println("other smt logic op") //[WIP] later error
														}
													}
													
													println(part.filter(_ == ')').size)
													if( part.contains(")")){
														opStack.pop
														println("Stacktop: " + opStack.top)
														if(in.size == inNow.size){
															println("SAME SIZE")
															var h = Seq.empty[String]
															for(n <- in.keys){
																h = h.concat(Seq(inNow.apply(in.apply(n))))
																//println(inNow.apply(in.apply(n)))
															}
															opInterp.apply(opNameNow).update(h.head, h.tail)
															inNow =	Map.empty[String, String]
															println(opInterp)
														}
													}
												}
											}
										}
									}
								}
							}
							case None => {
								println("no sorts")
							}
						}
					} else { //constants and functions
						sorts match {
							case Some(sortsMap: Map[String, Stack[String]]) => {
								//println("test constant: " + interpH.head)
								if((interpH.head.replace("(","").equals("as") & interpH.size == 3) | (opName(opNameNow).size == 1)) { //all mapped to the same elem or a constant
									opInterp.update(opNameNow, Map("default" -> Seq(interpH(1).replace("@", "").replace("$", "")), "all" -> Seq(interpH(1).replace("@", "").replace("$", ""))))
								} //else { //[WIP] HEREHEREHERE function with positive arity
							}
							case None => { //[WIP] error bc worlds
							}
						}
					}
				}
				case _ => {
					println("some other line in model")
					//throw new Exception("unexpected fol model structure in smt format")
				}
			}
		}
		val kripkemodel = KripkeModel.apply(modalDef, sorts, opName, opInterp)
		kripkemodel.printModel()
	}
	
}



object FOL2FOMLModelTranslator {
	def apply(modalDef: AnnotatedFormula, model: String, format: String): Unit = { //KripkeModel {
		println("go into fol2foml translator success")
		var modelH = model.split("\n").toSeq
		modelH = modelH.slice(1,modelH.size-1)
		val modeltranslator = new FOL2FOMLModelTranslator(modalDef, modelH)
		format match {
			case "smt" => {
				modeltranslator.smt()
				//println("format is smt")
			}
			case _ => {
				throw new Throwable("unknown fol model format during translation from fol to foml")
			}
		}
		
	}

}