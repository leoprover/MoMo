package MoMo

import leo.datastructures.TPTP
import leo.datastructures.TPTP.AnnotatedFormula
import leo.datastructures.TPTP.TFF._
import leo.modules.input.TPTPParser

final class TPTP2SMTTranslator(tptpForms: Seq[AnnotatedFormula]) {
	var smtDecl = ""
	var smtAx = ""
	var smtCon = ""
	def apply(): Seq[String] = {

		
		//*this part will be cleaned up/deleted 
//		for(formula <- tptpForms){
//				println(formula.pretty)
//				println("__________________________________________________")
//				println(formula.annotations)
//				println(formula.formula)
//				println("	", formula.formula.getClass)
//				println(formula.formulaType)
//				println(formula.name)
//				println(formula.role)
//				println(formula.symbols)
//				println("####################################################")
////			}

////			println("____TPTP TTYPE TO SMT SORT DECL________")
//		var smtSortDecl = "(declare-sort "
//			tptpForms(0).formula match {
//				case formulaTyp: TPTP.TFF.Typing => println(smtSortDecl + formulaTyp.atom.toString.replace("'", "") + " 0)")
//				case _ => println("is not typing")
////			}

////			println("____TPTP CONST TO SMT FUN DECL________")
//			//var smtFunDecl = "(declare-fun "
//			tptpForms(1).formula match {
//				case formulaTyp: TPTP.TFF.Typing => {
//					formulaTyp.typ match {
//						case atomicTyp: TPTP.TFF.AtomicType => {
//							val cSort = atomicTyp.name.toString.replace("'", "")
//							println(smtFunDecl + formulaTyp.atom.toString.replace("'", "") + " () " + cSort + ")")
//						}
//						case _ => println("not constant")
//					}
//
//				}
//				case _ => println("is not const decl")
////			}

//			println("____TPTP FUN TO SMT FUN DECL________")
//			tptpForms(2).formula match {
//				case formulaTyp: TPTP.TFF.Typing => {
//					formulaTyp.typ match {
//						case mapTyp: TPTP.TFF.MappingType => {
////							var outSort = ""
//							mapTyp.right match {
//								case out: TPTP.TFF.AtomicType => {
//									outSort =  out.name.toString.replace("'", "")
//								}
//								//case outList: Seq[Type] => println("returns more than just a constant/boolean")
//								case _ => println("idk sth wrong")
//
//							}
//							var inString = " ("
//							for(inMatch <- mapTyp.left) {
//								//println(inMatch.toString)
//								inMatch match {
//									case out: TPTP.TFF.AtomicType => {
//										inString +=  out.name.toString.replace("'", "") + " "
//									}
//									//case outList: Seq[Type] => println("returns more than just a constant/boolean")
//									case _ => println("idk sth wrong")
//								}
//								
//							}
//							inString = inString.dropRight(1) + ") "
//							println(smtFunDecl + formulaTyp.atom.toString.replace("'", "") + inString + outSort + ")")
//							
//						}
////						case _ => println("not function")
//					}
//
//				}
//				case _ => println("is not fun decl")
//			}

			//println("____TPTP FORMULA TO SMT FORMULA________")
			//var smtForm = ""
			
			//tptpForms(5).formula match {
			//	case tptpForm: TPTP.TFF.Logical => {
			//		if(tptpForms(5).role == "conjecture"){
			//			smtForm = tptp2smtFormula(tptpForm.formula, "(assert (not ")
			//			smtForm = smtForm + ")"
			//		} else {
			//			smtForm += tptp2smtFormula(tptpForm.formula, "(assert ")
			//		}
			//		smtForm += ")\n"
			//		
			//	}
			//	case _ => println("not formula")
			//}


//		println("____________________________________________")
		//*above will be deleted, below is what actually translates stuff

		if(tptpForms.mkString(" ").contains("$i")) {
			smtDecl += "(declare-sort $i 0)"
		}
			

		for(tptpForm <- tptpForms){
			//println(tptpForm)
			//println(tptpForm.role)
			tptpForm.role match { 
				case "axiom" => {
					tptpForm.formula match {
						case tptpAx: TPTP.TFF.Logical => {
							//println("*******************")
							//println(tptpAx.pretty)
							smtAx += tptp2smtFormula(tptpAx.formula, "(assert ")
							smtAx += ")\n"
							//println("##################")
						}
						case _ => {
							println("axiom but formula is not Logical")
						}
					}
				}
				case "conjecture" => {
					if(smtCon == ""){
						tptpForm.formula match {
							case tptpCon: TPTP.TFF.Logical => {
								smtCon = tptp2smtFormula(tptpCon.formula, "(assert (not ")
								smtCon += "))\n"
							}
							case _ => println("conjecture but formula is not Logical")
						}
					} else {
						println("more than one conjecture :(")
					}
				}
				
				case "type" => {
					tptpForm.formula match {
						case tptpTyp: Typing => {
							tptpTyp.typ match {
								case tptpAtom: AtomicType => {
									if(tptpAtom.name == "$tType"){
										smtDecl += "(declare-sort " + tptpTyp.atom.toString.replace("'", "") + " 0)\n" //[WIP] can be generalised to allow number > 0 (but also: how relevant will that be in this task?)
									} else {
										if(tptpAtom.name.toString.replace("'","") == "$o"){
											smtDecl += "(declare-fun " + tptpTyp.atom.toString.replace("'", "") + " () " + "Bool)\n"
										} else {
											smtDecl += "(declare-fun " + tptpTyp.atom.toString.replace("'", "") + " () " + tptpAtom.name.toString.replace("'","") + ")\n"
										}
									}
								}
								case tptpMap: MappingType => {
									var outSort = ""
									tptpMap.right match {
										case out: TPTP.TFF.AtomicType => {
											outSort =  out.name.toString.replace("'", "")
											if(outSort == "$o"){
												outSort = "Bool"
											}
										}
										//case outList: Seq[Type] => println("returns more than just a constant/boolean")
										case _ => println("idk sth wrong")

									}
									var inString = " ("
									for(inMatch <- tptpMap.left) {
										//println(inMatch.toString)
										inMatch match {
											case out: TPTP.TFF.AtomicType => {
												//inString +=  out.name.toString.replace("'", "") + " "
												if(out.name.toString == "$o"){
													inString += "Bool"
												} else {
													inString +=  out.name.toString.replace("'", "") + " "
												}
											}
											//case outList: Seq[Type] => println("returns more than just a constant/boolean")
											case _ => println("idk sth wrong")
										}
								
									}
									inString = inString.dropRight(1) + ") "
									//println(smtFunDecl + tptpTyp.atom.toString.replace("'", "") + inString + outSort + ")")
									smtDecl += "(declare-fun " + tptpTyp.atom.toString.replace("'", "") + inString + outSort + ")\n"
								}
								case _ =>{
									println("unexpected typ in Typing")
								}
							}
						}
						case _ => println("type but not a Typing")
					}
				}

				case _ => println("unsupported tptp role")
			}
		}
		//println("_________SMT AX__________")
		//println(smtAx)
		//println("_________SMT CON__________")
		//println(smtCon)
		//println("_________SMT DECL__________")
		//println(smtDecl)

		Seq(smtDecl, smtAx, smtCon)
			
	}

	def tptp2smtTerm(tptpTerm: Term, smtExpr: String): String = {
		var smtExprVar = smtExpr
		tptpTerm match {
			case tptpAtT: AtomicTerm => {

				if(tptpAtT.args.length > 0){
					smtExprVar += "(" + tptpAtT.f.replace("'", "") + " "
					for(atTArg <- tptpAtT.args){
						smtExprVar = tptp2smtTerm(atTArg, smtExprVar)
						smtExprVar += " "
					}
					smtExprVar += ")"
				} else {
					smtExprVar += tptpAtT.f.replace("'", "")
				}
				smtExprVar += " "	
			}
			case tptpVar: Variable => {
				smtExprVar += tptpVar.name + " "
			}
			case _ => println("different kind of term...")
		}
		return smtExprVar
	}
	
	def tptp2smtFormula(tptpForm: Formula, smtForm: String): String = {
		var smtFormVar = smtForm
		tptpForm match {
			case tptpAtF: AtomicFormula => {
				if(tptpAtF.args.length > 0) {
					smtFormVar += "(" + tptpAtF.f.replace("'", "") + " "
					for(atFArg <- tptpAtF.args){
						smtFormVar = tptp2smtTerm(atFArg, smtFormVar)
					}
					smtFormVar = smtFormVar.dropRight(1) + ")"
				} else {
					//smtFormVar += tptpAtF.f.replace("'", "").replace("$", "") 
					tptpAtF.f.replace("'", "") match {
						case "$true" => {
							smtFormVar += "true"
						}
						case "$false" => {
							smtFormVar += "false"
						}
						case _ => {
							smtFormVar += tptpAtF.f.replace("'", "")
						}
					}
				}
			}
			case tptpUna: UnaryFormula => {
				tptpUna.connective match {
					case ~ => {
						smtFormVar += "(not "
						smtFormVar = tptp2smtFormula(tptpUna.body, smtFormVar)
						smtFormVar += ")" 
					}
					case _ => {
						println("unknown unary connective")
					}
				}
			}
			case tptpBin: BinaryFormula => {
				tptpBin.connective match {
					case Impl => {
						smtFormVar += "(=> "
						smtFormVar = tptp2smtFormula(tptpBin.left, smtFormVar) + " "
						smtFormVar = tptp2smtFormula(tptpBin.right, smtFormVar)
						smtFormVar += ")"
					}
					case & => {
						smtFormVar += "(and "
						smtFormVar = tptp2smtFormula(tptpBin.left, smtFormVar) + " "
						smtFormVar = tptp2smtFormula(tptpBin.right, smtFormVar)
						smtFormVar += ")"
					}
					case | => {
						smtFormVar += "(or "
						smtFormVar = tptp2smtFormula(tptpBin.left, smtFormVar) + " "
						smtFormVar = tptp2smtFormula(tptpBin.right, smtFormVar)
						smtFormVar += ")"
					}
					case <=> => {
						smtFormVar += "(= "
						smtFormVar = tptp2smtFormula(tptpBin.left, smtFormVar) + " "
						smtFormVar = tptp2smtFormula(tptpBin.right, smtFormVar)
						smtFormVar += ")"
					}
					case <= => {
						smtFormVar += "(=> "
						smtFormVar = tptp2smtFormula(tptpBin.right, smtFormVar) + " "
						smtFormVar = tptp2smtFormula(tptpBin.left, smtFormVar)
						smtFormVar += ")"
					}
					case _ => {
						println("unknown binary connective")
					}
				}
			}
			case tptpQuant: QuantifiedFormula => {
				tptpQuant.quantifier match {
					case ! => {
						smtFormVar += "(forall ("
					}
					case ? => {
						smtFormVar += "(exists ("
					}
					case _ => {
						println("unknown quantifier")
					}
				}
				
				for(quantVar <- tptpQuant.variableList){
					smtFormVar += "(" + quantVar._1 + " "
					quantVar._2 match {
						case Some(varType) => {
							varType match {
								case varType: AtomicType => {
									//println("atomic type variable")
									//println(varType.name)
									smtFormVar += varType.name.toString.replace("'", "") + ") "
								}
								case _ => {
									println("not an atomic type") //MappingType(_, _), QuantifiedType(_, _), TupleType(_), TypeVariable(_)
								}
							}
						}
						case _ => println("probably needs type inference?")
					}	
				}

				smtFormVar = smtFormVar.dropRight(1) + ") "

				smtFormVar = tptp2smtFormula(tptpQuant.body, smtFormVar)
				smtFormVar += ")"			

			}
			case tptpEqual: Equality => {
				smtFormVar += "(= "
				smtFormVar = tptp2smtTerm(tptpEqual.left, smtFormVar) + " "
				smtFormVar = tptp2smtTerm(tptpEqual.right, smtFormVar)
				smtFormVar += ")"
				
			}
			case tptpIneq: Inequality => {
				smtFormVar += "(not (= "
				tptpIneq.left match {
					case ineqTerm: Term => {
						smtFormVar = tptp2smtTerm(ineqTerm, smtFormVar) + " "
					}
					case _ => {
						println("Ineq without terms as args")
					}
				}
				tptpIneq.right match {
					case ineqTerm: Term => {
						smtFormVar = tptp2smtTerm(ineqTerm, smtFormVar)
					}
					case _ => {
						println("Ineq without terms as args")
					}
				}
				smtFormVar += "))"
			}
			case _ => {
				println("sth else")
				println(tptpForm.getClass)
			}	
		}
		return smtFormVar
	}

}

object TPTP2SMTTranslator {

	def apply(tptpForm: TPTP.Problem): Seq[String] = {
		val translator2smt = new TPTP2SMTTranslator(tptpForm.formulas)
		translator2smt.apply()
	}


}