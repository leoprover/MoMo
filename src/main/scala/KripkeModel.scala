package MoMo

import leo.datastructures.TPTP
import leo.datastructures.TPTP.AnnotatedFormula
import leo.datastructures.TPTP.TFFAnnotated
import leo.datastructures.TPTP.TFF._
import leo.modules.input.TPTPParser

import scala.collection.mutable.Map
import scala.collection.mutable.Stack //maybe i'll change this to a queue just bc i prefer that order in the model

		//probDecl should probably loose Option since prop/pred/func/const will have to be declared?                     //actually, domains should be optioned
class KripkeModel(modalDef: AnnotatedFormula, probDecl: Option[Seq[AnnotatedFormula]], modelDecl: Option[Seq[AnnotatedFormula]], interpDomains: AnnotatedFormula, interpWorlds: AnnotatedFormula, interpMappings: AnnotatedFormula){ // 

	def printModel(){
	//prints model
		println(modalDef.pretty)
		probDecl match {
			case Some(probSeq: Seq[AnnotatedFormula]) => {
				for(decl <- probSeq) {
					println(decl.pretty)
				}
			}
			case None => {
				println("%no user decl sorts") 
			}
		}
		println("")
		modelDecl match {
			case Some(modelSeq: Seq[AnnotatedFormula]) => {
				for(decl <- modelSeq) {
					println(decl.pretty)
				}
			}
			case None => {
				println("frame incomplete, error") //[WIP] shouldn't happen bc worlds always exist that need to be decl
			}
		}
		println("")

		println(interpWorlds.pretty)
		println("")
		//[WIP] print domain interp prettily
		//var domainSplit = interpDomains.pretty.split("\\(! \\[W:\\$world\\]: \\(\\$in_world\\(W,")
		//println("_________________")
		//println(domainSplit.mkString("\n"))
		//println("_________________")
		//println(domainSplit.head)
		//for(dom <- domainSplit.drop(1)) {
		//	println("(! [W:$world]: ($in_world(W,")
		//	println("	" + dom.split("&").filterNot(Set(" ")).mkString("\n	& "))
		//}
		println(interpDomains.pretty)
		println("")
		println(interpMappings.pretty)
		
	}
	
} 

object KripkeModel{
	def apply(modalDef: AnnotatedFormula, sorts: Option[Map[String, Stack[String]]], opName: Map[String, Seq[String]], opInterp: Map[String, Map[String, Seq[String]]]): KripkeModel = { 
	//sorts: sort name > domain element names; op_name: user decl operation name > (func,const: neg arity+1, pred,prop: pos arity+1); op_interp: user decl. operation name > interpretation in each world
	//[WIP] error handling over all, also with how TPTPParser is used
	//write into TPTP datastructures for const domain

		println("get into KripkeModel success")
		//problem symbol declaration
		var probDecl = Seq.empty[AnnotatedFormula]
		var modelDecl = Seq.empty[AnnotatedFormula]
		//var interpDomains = Seq.empty[AnnotatedFormula]
		var domH = "tff(model_domains, interpretation-domains,\n("
		var worldH = "tff(model_frame, interpretation-worlds,\n("
		var interpH =  "tff(model_mappings, interpretation-mappings, \n("
		
		sorts match {
			case Some(sortsMap: Map[String, Stack[String]]) => {
				for(sort <- sortsMap.keys) {
					println(sort)
					//form annotated formulas for declaration of problem sort symbols
					//and form annotated formulas for additional model symbols
					if(sort != "$world" & sort != "$i"){
						//println(sort)
						probDecl = probDecl.concat(Seq(TPTPParser.annotatedTFF("tff(" + sort + "_decl, type, " + sort + ": $tType).")))
						modelDecl = modelDecl.concat(Seq(TPTPParser.annotatedTFF("tff(d_" + sort + "_decl, type, d_" + sort + ": $tType).")))
						modelDecl = modelDecl.concat(Seq(TPTPParser.annotatedTFF( "tff(d2" + sort + "_decl, type, d2" + sort + ": d_" + sort + " > " + sort + ")." )))
					}

					for(elem <- sortsMap(sort)){
						//println(elem)
						if(sort != "$world" & sort != "$i"){
							//println(sort)
							modelDecl = modelDecl.concat(Seq(TPTPParser.annotatedTFF("tff(d_" + elem + "_decl, type, d_" + elem + ": d_" + sort + ").")))
						} else {
							modelDecl = modelDecl.concat(Seq(TPTPParser.annotatedTFF("tff(" + elem + "_decl, type, " + elem + ": " + sort + ").")))
						}
					}

					//form annotated formulas for domain definition

					if(sort != "$world"){
						if(sortsMap(sort).length > 1){
							domH += "$distinct(" + sortsMap(sort).mkString(", ") + ")\n& "
							//println(domH)
						}
						if(modalDef.pretty.contains("$constant")){ //for constant domains
							domH += constD(sort, sortsMap(sort))
						} else { //for varying domains
							if(opInterp.apply("$exists_in_world_" + sort).size > 1) { //domains differ in at least two worlds => all domains are listed per world
								domH += varyD(sort, opInterp("$exists_in_world_" + sort), sortsMap(sort), sortsMap("$world"))
								println("exit domain construction")
							} else { //domains are effectively constant
								opInterp("$exists_in_world_" + sort).apply("default").head match {
									case "$true" => {
										domH += constD(sort, sortsMap(sort))
									}
									case "$false" => { //[WIP] shouldn't happen bc then no elements exist in any world => error when specifying 
										println("no elements in any world. specifying $exists_in_world_" + sort + " must have been faulty.")
									}
								println("exit domain construction")
								}
							}
						}

					} else {
						if(sortsMap(sort).length > 1){
							worldH += "$distinct(" + sortsMap(sort).mkString(", ") + ")\n& "
						}
						worldH +=  sortsMap(sort).mkString("(![W: $world]: ((W = ", ") | (W = ", ")))\n& ")
						println(worldH)
					}

				}
				
			}
			case None => {
				println("no sorts") //[WIP] should be error bc $world should always be in sorts
			}
		}

		var interpWM = Map.empty[String, String]
		for(opNN <- opName.keys) {
			opNN match {
				case "$accessible_world" => {
					var worldD = "(! [W1: $world, W2: $world]: (~("
					opInterp.apply(opNN).apply("default").head match {
						case "$true" => {
							while(opInterp.apply(opNN).apply("all").nonEmpty){
								var (h1, h2) = opInterp.apply(opNN).apply("all").splitAt(2)
								opInterp.apply(opNN).update("all", h2)
								//println(h1)
								//println(opInterp.apply(opNN).apply("all"))
								worldH += h1.mkString("~$accessible_world(", ", ", ")\n& ")
								worldD += h1.mkString("(W1 = ", " & W2 = ", ") | ")
							}
							worldH += worldD.dropRight(3) + ") => $accessible_world(W1, W2)))\n& "
						}
						case "$false" => {
							while(opInterp.apply(opNN).apply("all").nonEmpty){
								var (h1, h2) = opInterp.apply(opNN).apply("all").splitAt(2)
								opInterp.apply(opNN).update("all", h2)
								//println(h1)
								//println(opInterp.apply(opNN).apply("all"))
								worldH += h1.mkString("$accessible_world(", ", ", ")\n& ")
								worldD += h1.mkString("(W1 = ", " & W2 = ", ") | ")
							}
							worldH += worldD.dropRight(3) + ") => ~$accessible_world(W1, W2)))\n& "
						}
					}
					println(worldH)
				}
				case "$local_world" => {
					worldH += opNN + " = " + opInterp.apply(opNN).apply("all").head + "\n& "
				}
				case op if op.contains("$exists_in_world") => { //nothing to do
				}
				case _ => {
					//problem symbol declaration and interpretations for non-sort user decl symbols
					Seq(opName(opNN).size, opName(opNN).head) match {
						case Seq(a: Int, b: String) if (a > 2 & b == "$o") => {//predicate symbol of arity a-2
							//add symbol to problem decl.
							probDecl = probDecl.concat(Seq(TPTPParser.annotatedTFF("tff(" + opNN + "_decl, type, " + opNN + ": " + opName(opNN).tail.filterNot(s => s.equals("$world")).mkString("(", " * ", ") > ") + "$o).")))
							//add interpretation
							sorts match {
								case Some(sortsMap: Map[String, Stack[String]]) => {
									opInterp(opNN)("default").head match {
										case "$true" => {
										
										}
										case "$false" => {
											for(world <- sortsMap("$world")) {
												interpWM.update(world, "")
												var h = ""
												//interpH += "in_world(" + world + ", \n("
												if(opInterp.apply(opNN).keys.toSeq.contains(world)){
													while(opInterp.apply(opNN).apply(world).nonEmpty){
														var (h1, h2) = opInterp.apply(opNN).apply(world).splitAt(a-1)
														opInterp.apply(opNN).update(world, h2)

														interpWM(world) = interpWM(world) + opNN + h1.mkString("(", ", ", ")\n& ")
														for(n <- 0 until a-2) {
															//println("n: " + n.toString)
															h += "(O" + (n+1).toString + " = " + h1(n) + " & "
														}
														h = h.dropRight(3) + ") | "
													}
													h = h.dropRight(3)
													interpWM(world) = interpWM(world) +  "(! ["
													for(n <- 0 until a-2){
														interpWM(world) = interpWM(world) + "O" + (n+1).toString + ": " + opName(opNN)(n+2) + ", "
													}
													interpWM(world) = interpWM(world).dropRight(2) + "]: (( ~(" + h + ") => ~" + opNN + "("
													for(n <- 0 until a-2){
														interpWM(world) = interpWM(world) + "O" + (n+1).toString + ", "
													}
													interpWM(world) = interpWM(world).dropRight(2) + "))))\n& " 
												} else {
													interpWM(world) = interpWM(world) + "(! ["
													for(n <- 0 until a-2){
														interpWM(world) = interpWM(world) + "O" + (n+1).toString + ": " + opName(opNN)(n+2) + ", "
													}
													interpWM(world) = interpWM(world).dropRight(2) + "]: ~" + opNN + "("
													for(n <- 0 until a-2){
														interpWM(world) = interpWM(world) + "O" + (n+1).toString + ", "
													}
													interpWM(world) = interpWM(world).dropRight(2) + "))\n& " 
												}
												//println("INTERP WORLD: " + interpWM(world))
											}
										}
									}
								}

								
							}

						}
						case Seq(a: Int, b: String) if (a == 2 & b == "$o") => {//propositional symbol (a == 2 bc opName(opNN) = (output_sort, $world))
							//add symbol to problem decl.
							probDecl = probDecl.concat(Seq(TPTPParser.annotatedTFF("tff(" + opNN + "_decl, type, " + opNN + ": $o).")))
						}
						case Seq(a: Int, b: String) if (a == 1 & b != "$o") => {//constant symbol //[WIP] strucutre needs to be adjusted when flexible func/const allowed
							//add symbol to problem decl.
							probDecl = probDecl.concat(Seq(TPTPParser.annotatedTFF("tff(" + opNN + "_decl, type, " + opNN + ": " + b + ").")))
						}
						case Seq(a: Int, b: String) if (a > 1 & b != "$o") => {//function of arity a-1
							//add symbol to problem decl.
							probDecl = probDecl.concat(Seq(TPTPParser.annotatedTFF("tff(" + opNN + "_decl, type, " + opNN + ": " + opName(opNN).tail.mkString("(", " * ", ") > ") + b + ").")))
						}

					
					}
					
				}
			}
		}

		//println(domH)
		domH = domH.dropRight(2) + "))."
		//println(domH)

		//println(worldH)
		worldH = worldH.dropRight(2) + "))."
		//println(worldH)

		//println(interpH)
		sorts match {
			case Some(sortsMap: Map[String, Stack[String]]) => {
				for(world <- sortsMap("$world")) {
					interpH += "$in_world(" + world + ", \n" + interpWM(world).dropRight(3) + " )\n& "
				}
			}
			case None => {
			}
		}
		interpH = interpH.dropRight(2) + "))."
		println(interpH)

		if(probDecl.isEmpty){ //some problem symbols should always exist, right? like, a prop symbol or sth //I think this can be solved better if check empty -> make modelDecl to None OR rather work with it as option from the beginning
			if(modelDecl.isEmpty){
				val model = new KripkeModel(modalDef,None, None, TPTPParser.annotatedTFF(domH), TPTPParser.annotatedTFF(worldH), TPTPParser.annotatedTFF(interpH))
				return model
				//model.printModel()
			} else {
				val model = new KripkeModel(modalDef,None, Some(modelDecl), TPTPParser.annotatedTFF(domH), TPTPParser.annotatedTFF(worldH), TPTPParser.annotatedTFF(interpH))
				return model
				//model.printModel()
			}
		} else {
			if(modelDecl.isEmpty){
				val model = new KripkeModel(modalDef,Some(probDecl), None, TPTPParser.annotatedTFF(domH), TPTPParser.annotatedTFF(worldH), TPTPParser.annotatedTFF(interpH))
				return model
				//model.printModel()
			} else {
				val model = new KripkeModel(modalDef,Some(probDecl), Some(modelDecl), TPTPParser.annotatedTFF(domH), TPTPParser.annotatedTFF(worldH), TPTPParser.annotatedTFF(interpH))
				return model
				//model.printModel()
			}
		}

	}

				//sortsMap(sort)
	def constD(sort: String, domainU: Stack[String]): String = {
		var domH = ""
		//if(domainU.length > 1){
		//	domH += "$distinct(" + domainU.mkString(", ") + ")\n& "
			//println(domH)
		//}
		domH += "(![W: $world]: ($in_world(W,\n	("
		if(sort != "$i") {
		////bijective promotion func
			domH += "(![O: " + sort + "]: (?[DO: d_" + sort + "]: (O = d2" + sort + "(DO))))\n	& "
			domH += "(![DO1: d_" + sort + ", DO2: d_" + sort + "]: ( (d2" + sort + "(DO1) = d2" + sort + "(DO2)) => (DO1 = DO2) ))\n	& "
		////each domain element of model sort is rep by one domain element symbol
			domH += "(![DO: d_" + sort + "]: ( (" + domainU.mkString("DO = ", ") | (DO = ", ") ))\n	& ")
		////there is a domain element of model sort that corresponds to each domain element symbol
			domH += domainU.mkString("(?[DO: d_" + sort + "]: (DO = d_", "))\n	& (?[DO: d_" + sort + "]: (DO = d_", "))))))\n &")
		} else {
		////each domain element of model sort is rep by one domain element symbol
			domH += "(![DO: " + sort + "]: ( (" + domainU.mkString("DO = ", ") | (DO = ", ") ))\n	& ")
		////there is a domain element of model sort that corresponds to each domain element symbol
			domH += domainU.mkString("(?[DO: " + sort + "]: (DO = ", "))\n	& (?[DO: " + sort + "]: (DO = ", "))))))\n &")
		}

		return domH
	}
	def varyD(sort: String, existMap: Map[String, Seq[String]], domainU: Stack[String], worldSet: Stack[String]): String = {
		println("enter varying domain construction success")
		var domH = ""
		if(sort != "$i") {
			existMap("default").head match {
				case "$true" => {
					for(world <- worldSet) {
						existMap.get(world) match {
							case Some(existWorld: Seq[String]) => {
								domH += "($in_world(" + world + ",\n	("
								////bijective promotion func
								domH += "(![O: " + sort + "]: (?[DO: d_" + sort + "]: (O = d2" + sort + "(DO))))\n	& "
								domH += "(![DO1: d_" + sort + ", DO2: d_" + sort + "]: ( (d2" + sort + "(DO1) = d2" + sort + "(DO2)) => (DO1 = DO2) ))\n	& "
	
								////each domain element of model sort is rep by one domain element symbol
								var h = domainU.filter(s => !existMap.keys.toSeq.contains(s))
								domH += "(![DO: d_" + sort + "]: ( (" + h.mkString("DO = ", ") | (DO = ", ") ))\n	& ")
								////there is a domain element of model sort that corresponds to each domain element symbol
								domH += h.mkString("(?[DO: d_" + sort + "]: (DO = ", "))\n	& (?[DO: " + sort + "]: (DO = ", ")))))\n &")
								
							}
							case None => {
								domH += "($in_world(" + world + ",\n	("
								////bijective promotion func
								domH += "(![O: " + sort + "]: (?[DO: d_" + sort + "]: (O = d2" + sort + "(DO))))\n	& "
								domH += "(![DO1: d_" + sort + ", DO2: d_" + sort + "]: ( (d2" + sort + "(DO1) = d2" + sort + "(DO2)) => (DO1 = DO2) ))\n	& "

								////each domain element of model sort is rep by one domain element symbol
								domH += "(![DO: d_" + sort + "]: ( (" + domainU.mkString("DO = ", ") | (DO = ", ") ))\n	& ")
								////there is a domain element of model sort that corresponds to each domain element symbol
								domH += domainU.mkString("(?[DO: d_" + sort + "]: (DO = d_", "))\n	& (?[DO: d_" + sort + "]: (DO = d_", ")))))\n &")
								
							}
						}
					}
				}
				case "$false" => {
					for(world <- worldSet) {
						existMap.get(world) match {
							case Some(existWorld: Seq[String]) => {
								domH += "($in_world(" + world + ",\n	("
								////bijective promotion func
								domH += "(![O: " + sort + "]: (?[DO: d_" + sort + "]: (O = d2" + sort + "(DO))))\n	& "
								domH += "(![DO1: d_" + sort + ", DO2: d_" + sort + "]: ( (d2" + sort + "(DO1) = d2" + sort + "(DO2)) => (DO1 = DO2) ))\n	& "
		
								////each domain element of model sort is rep by one domain element symbol
								domH += "(![DO: d_" + sort + "]: ( (" + existWorld.mkString("DO = ", ") | (DO = ", ") ))\n	& ")
								////there is a domain element of model sort that corresponds to each domain element symbol
								domH += existWorld.mkString("(?[DO: d_" + sort + "]: (DO = ", "))\n	& (?[DO: " + sort + "]: (DO = ", ")))))\n &")
							}
							case None => {//[WIP] should error bc then domain in this world empty
								println("no elements of " + sort + " in " + world)
								
							}
						}
					}
				}
			}

		} else {
			existMap("default").head match {
				case "$true" => {
					for(world <- worldSet) {
						existMap.get(world) match {
							case Some(existWorld: Seq[String]) => {
								domH += "($in_world(" + world + ",\n	("

								////each domain element of model sort is rep by one domain element symbol
								var h = domainU.filter(s => !existMap.keys.toSeq.contains(s))
								domH += "(![DO: " + sort + "]: ( (" + h.mkString("DO = ", ") | (DO = ", ") ))\n	& ")
								////there is a domain element of model sort that corresponds to each domain element symbol
								domH += h.mkString("(?[DO: " + sort + "]: (DO = ", "))\n	& (?[DO: " + sort + "]: (DO = ", ")))))\n &")
								
							}
							case None => {
								domH += "($in_world(" + world + ",\n	("

								////each domain element of model sort is rep by one domain element symbol
								domH += "(![DO: " + sort + "]: ( (" + domainU.mkString("DO = ", ") | (DO = ", ") ))\n	& ")
								////there is a domain element of model sort that corresponds to each domain element symbol
								domH += domainU.mkString("(?[DO: " + sort + "]: (DO = ", "))\n	& (?[DO: " + sort + "]: (DO = ", ")))))\n &")
								
							}
						}
					}
				}
				case "$false" => {
					for(world <- worldSet) {
						existMap.get(world) match {
							case Some(existWorld: Seq[String]) => {
								domH += "($in_world(" + world + ",\n	("

								////each domain element of model sort is rep by one domain element symbol
								domH += "(![DO: " + sort + "]: ( (" + existWorld.mkString("DO = ", ") | (DO = ", ") ))\n	& ")
								////there is a domain element of model sort that corresponds to each domain element symbol
								domH += existWorld.mkString("(?[DO: " + sort + "]: (DO = ", "))\n	& (?[DO: " + sort + "]: (DO = ", ")))))\n &")
							}
							case None => {//[WIP] should error bc then domain in this world empty
								println("no elements of " + sort + " in " + world)
								
							}
						}
					}
				}
			}
		}

		return domH
	}

}