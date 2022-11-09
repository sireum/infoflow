// #Sireum
package org.sireum.logika.infoflow

import org.sireum._
import org.sireum.lang.ast.Exp.InfoFlowInvariant
import org.sireum.lang.ast.MethodContract.InfoFlow
import org.sireum.lang.ast.{Exp, Stmt, Transformer}
import org.sireum.lang.symbol.TypeInfo
import org.sireum.lang.tipe.TypeHierarchy
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.{Reporter, Split}
import org.sireum.logika.State.Claim
import org.sireum.logika.State.Claim.Let
import org.sireum.logika.Util.{checkMethodPost, checkMethodPre, logikaMethod, updateInVarMaps}
import org.sireum.logika.infoflow.InfoFlowContext.{FlowCheckType, InfoFlowAgreeSym, InfoFlowsType}
import org.sireum.logika.plugin.{ClaimPlugin, MethodPlugin, Plugin, StmtPlugin}
import org.sireum.logika.{Config, Logika, Smt2, State, Util}
import org.sireum.message.Position

object InfoFlowPlugins {
  val defaultPlugins: ISZ[Plugin] = ISZ(InfoFlowMethodPlugin(), InfoFlowInlineAgreeStmtPlugin(), InfoFlowLoopStmtPlugin(), InfoFlowClaimPlugin())
}

@datatype class InfoFlowMethodPlugin extends MethodPlugin {

  @pure def name: String = {
    return "Info Flow Method Plugin"
  }

  @pure def canHandle(th: TypeHierarchy, method: AST.Stmt.Method): B = {
    method.contract match {
      case c: AST.MethodContract.Simple => return c.infoFlows.nonEmpty
      case _ => return F
    }
  }

  @pure def handle(th: TypeHierarchy,
                   plugins: ISZ[Plugin],
                   method: AST.Stmt.Method,
                   caseIndex: Z,
                   config: Config,
                   smt2: Smt2,
                   cache: Smt2.Cache,
                   reporter: Reporter): B = {

    val mconfig: Config = if (caseIndex >= 0) config(checkInfeasiblePatternMatch = F) else config

    def checkCase(labelOpt: Option[AST.Exp.LitString], reads: ISZ[AST.Exp.Ref], requires: ISZ[AST.Exp],
                  modifies: ISZ[AST.Exp.Ref], ensures: ISZ[AST.Exp], infoFlowsNode: ISZ[InfoFlow]): Unit = {
      var state = State.create
      labelOpt match {
        case Some(label) if label.value != "" => state = state.addClaim(State.Claim.Label(label.value, label.posOpt.get))
        case _ =>
      }
      val res = method.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      val methodPosOpt = method.sig.id.attr.posOpt
      var logika: Logika = {
        val receiverTypeOpt: Option[AST.Typed] = if (res.isInObject) {
          None()
        } else {
          th.typeMap.get(res.owner).get match {
            case ti: TypeInfo.Sig => Some(ti.tpe)
            case ti: TypeInfo.Adt => Some(ti.tpe)
            case _ => halt("Infeasible")
          }
        }
        val p = updateInVarMaps(logikaMethod(th, mconfig, res.owner, method.sig.id.value, receiverTypeOpt, method.sig.paramIdTypes,
          method.sig.returnType.typedOpt.get, methodPosOpt, reads, requires, modifies, ensures,
          if (labelOpt.isEmpty) ISZ() else ISZ(labelOpt.get), plugins, None(), HashSet.empty), smt2, cache, state, reporter)
        state = p._2
        p._1
      }
      val invs = logika.retrieveInvs(res.owner, res.isInObject)
      state = checkMethodPre(logika, smt2, cache, reporter, state, methodPosOpt, invs, requires)

      var infoFlows: InfoFlowsType = HashSMap.empty[String, InfoFlow]
      for(infoFlow <- infoFlowsNode) {
        if(infoFlows.contains(infoFlow.label.value)) {
          reporter.error(infoFlow.label.posOpt, name, "Flow case channels must be unique")
        }
        infoFlows = infoFlows + infoFlow.label.value ~> infoFlow
      }

      if(reporter.hasError) {
        return
      }

      val stateSyms = InfoFlowUtil.processInfoFlowInAgrees(infoFlows, logika, smt2, cache, reporter, state)
      state = stateSyms._1

      logika = InfoFlowContext.putInfoFlowsL(infoFlows, logika)
      logika = InfoFlowContext.putInAgreementsL(stateSyms._2, logika)

      val stmts = method.bodyOpt.get.stmts
      val ss: ISZ[State] = if (method.purity == AST.Purity.StrictPure) {
        halt("Infeasible since contracts cannot be attached to strict pure methods")
      } else {
        logika.evalStmts(Split.Default, smt2, cache, None(), T, state, stmts, reporter)
      }

      val augInAgrees = InfoFlowContext.getInAgreements(logika.context.storage).get

      val flowChecks: ISZ[FlowCheckType] = infoFlows.values.map((m: InfoFlow) => ((m.label.value, m.label.posOpt, m.outAgrees)))
      val ss2: ISZ[State] = InfoFlowUtil.checkInfoFlowAgreements(infoFlows, augInAgrees, flowChecks,
        "Post Flow: ",
        logika, smt2, cache, reporter, ss)

      val ssPost: ISZ[State] = checkMethodPost(logika, smt2, cache, reporter, ss2, methodPosOpt, invs, ensures, mconfig.logPc, mconfig.logRawPc,
        if (stmts.nonEmpty) stmts(stmts.size - 1).posOpt else None())
    }

    method.mcontract match {
      case contract: AST.MethodContract.Simple =>
        checkCase(None(), contract.reads, contract.requires, contract.modifies, contract.ensures, contract.infoFlows)
      case contract: AST.MethodContract.Cases =>
        halt("Infeasible until Cases include InfoFlows")
    }

    return T
  }
}

object InfoFlowInlineAgreeStmtPlugin {
  @datatype class InlineCheck() extends Transformer.PrePost[B] {
    override def preExpInlineAgree(ctx: B, o: AST.Exp.InlineAgree): Transformer.PreResult[B, Exp] = {
      return Transformer.PreResult(T, F, None())
    }
  }
}

@datatype class InfoFlowInlineAgreeStmtPlugin extends StmtPlugin {

  @pure def name: String = {
    return "Info Flow Inline Agreement Statement Plugin"
  }

  @pure def canHandle(logika: Logika, stmt: AST.Stmt): B = {

    return InfoFlowContext.getInfoFlows(logika.context.storage).nonEmpty &&
      InfoFlowContext.getInAgreements(logika.context.storage).nonEmpty &&
      stmt.isInstanceOf[AST.Stmt.DeduceSequent] &&
      Transformer(InfoFlowInlineAgreeStmtPlugin.InlineCheck()).transformStmt(F, stmt).ctx
  }

  @pure def handle(logika: Logika,
                   smt2: Smt2,
                   cache: Smt2.Cache,
                   state: State,
                   stmt: AST.Stmt,
                   reporter: Reporter): ISZ[State] = {
    val infoFlows = InfoFlowContext.getInfoFlows(logika.context.storage).get
    val inAgrees = InfoFlowContext.getInAgreements(logika.context.storage).get

    var states: ISZ[State] = ISZ(state)
    stmt match {
      case AST.Stmt.DeduceSequent(None(), sequents) =>
        for (sequent <- sequents) {
            sequent match {
              case AST.Sequent(ISZ(), e: AST.Exp.InlineAgree, ISZ()) =>
                infoFlows.get(e.channel.value) match {
                  case Some(infoFlow) =>
                    val outAgrees: ISZ[Exp] = if (e.outAgrees.nonEmpty) e.outAgrees else infoFlow.outAgrees
                    states = InfoFlowUtil.checkInfoFlowAgreements(
                      infoFlows, inAgrees, ISZ((e.channel.value, e.channel.posOpt, outAgrees)),
                      "Inline Flow Agreement: ", logika, smt2, cache, reporter, states)
                  case _ =>
                    reporter.error(e.channel.posOpt, name, s"'${e.channel.value}' is not an existing channel")
                }

              case AST.Sequent(_, _: AST.Exp.InlineAgree, _) =>
                reporter.error(stmt.posOpt, name, "Sequents containing inline agreements cannot contain premises or steps")
              case _ =>
                reporter.error(stmt.posOpt, name, "Inline agreements must appear as the conclusion of a sequent and cannot be combined with functional contracts")
            }
        }
      case AST.Stmt.DeduceSequent(Some(_), _) =>
        reporter.error(stmt.posOpt, name, "Justifications disallowed for deduce statements with inline agreements")
      case _ =>
        halt("Infeasible")
    }
    if(reporter.hasError) {
      states = states.map((s: State) => s(status = F))
    }
    return states
  }
}

object InfoFlowLoopStmtPlugin {
  @datatype class ContainsFlowLoopInvariant() extends Transformer.PrePost[B] {
    override def preExpInfoFlowInvariant(ctx: B, o: InfoFlowInvariant): Transformer.PreResult[B, Exp] = {
      return Transformer.PreResult(T, F, None())
    }
  }

  @memoize def getFlowLoopInvariants(invariants: ISZ[AST.Exp]): ISZ[AST.Exp] = {
    return ops.ISZOps(invariants).filter((i: AST.Exp) => Transformer(ContainsFlowLoopInvariant()).transformExp(F, i).ctx)
  }
}

@datatype class InfoFlowLoopStmtPlugin extends StmtPlugin {
  @pure def name: String = {
    return "Info Flow Loop Statement Plugin"
  }

  @pure def canHandle(logika: Logika, stmt: Stmt): B = {
    stmt match {
      case whileStmt: AST.Stmt.While =>
        return InfoFlowLoopStmtPlugin.getFlowLoopInvariants(whileStmt.invariants).nonEmpty &&
          InfoFlowContext.getInfoFlows(logika.context.storage).nonEmpty &&
          InfoFlowContext.getInAgreements(logika.context.storage).nonEmpty
      case _ => return F
    }
  }

  def recordLoopInvariantOutAgrees(state: State, invariantFlows: InfoFlowsType, pos: Option[Position], reporter: Reporter): State = {
    var s = state
    for (infoFlow <- invariantFlows.values) {
      val channel = infoFlow.label.value
      var syms: ISZ[State.Value.Sym] = ISZ()
      var agreeClaims: ISZ[State.Claim] = ISZ()
      for (outExp <- infoFlow.outAgrees) {
        outExp match {
          case ref: AST.Exp.Ref =>
            val res = ref.resOpt.get
            res match {
              case lv: AST.ResolvedInfo.LocalVar =>
                val (s1, r) = Util.idIntro(ref.posOpt.get, s, lv.context, s"${lv.id}", ref.typedOpt.get, None())
                syms = syms :+ r
                agreeClaims = agreeClaims :+ State.Claim.Custom(InfoFlowAgreeSym(r, lv.id, channel))
                s = s1
              case x => halt(s"Need to handle $x")
            }
          case x => halt(s"Need to handle : $x")
        }
      }
      s = s(claims = s.claims ++ agreeClaims)
    }
    return s
  }

  @pure def handle(logikax: Logika, smt2: Smt2, cache: Smt2.Cache, s0: State, stmt: Stmt, reporter: Reporter): ISZ[State] = {
    stmt match {
      case whileStmt: AST.Stmt.While =>
        InfoFlowLoopStmtPlugin.getFlowLoopInvariants(whileStmt.invariants) match {
          case ISZ(flowInvariant: AST.Exp.InfoFlowInvariant) => {

            var logika = logikax

            val split = Split.Default // TODO: argument to evalStmt that's lost when calling plugin
            val rtCheck: B = F // TODO: argument to evalStmt that's lost when calling plugin

            var r = ISZ[State]()

            val methodInAgreements = InfoFlowContext.getInAgreements(logika.context.storage).get

            val invariantFlows: InfoFlowsType = HashSMap.empty[String, InfoFlow] ++ flowInvariant.flowInvariants.map((m: InfoFlow) => ((m.label.value, m)))

            val loopPartitionsToCheck: ISZ[FlowCheckType] = invariantFlows.values.map((m: InfoFlow) => {
              if(!methodInAgreements.contains(m.label.value)) {
                reporter.error(m.label.posOpt, name, s"'${m.label.value}' is not an existing channel'")
              }
              ((m.label.value, m.label.posOpt, m.outAgrees))
            })

            if (reporter.hasError) {
              return r :+ s0(status = F)
            }

            val nonFlowInvariants = whileStmt.invariants.filter((e: Exp) => !e.isInstanceOf[InfoFlowInvariant])

            val postInvStates = logika.checkExps(split, smt2, cache, F, "Loop invariant", " at the beginning of while-loop", s0,
              nonFlowInvariants, reporter)

            for (s0w <- InfoFlowUtil.checkInfoFlowAgreements(
              invariantFlows, methodInAgreements, loopPartitionsToCheck,
              "Flow Loop Invariant at the beginning of while-loop: ",
              logika, smt2, cache, reporter, postInvStates)) {

              if (s0w.status) {

                val flowInAgrees = InfoFlowUtil.processInfoFlowInAgrees(invariantFlows,
                  logika, smt2, cache, reporter, s0w)

                logika = InfoFlowContext.putInAgreementsL(flowInAgrees._2, logika)

                val s1 = flowInAgrees._1
                val s0R: State = {
                  val modObjectVars = whileStmt.contract.modifiedObjectVars
                  var srw = Util.rewriteObjectVars(logika, smt2, cache, rtCheck, s0(nextFresh = s1.nextFresh),
                    whileStmt.contract.modifiedObjectVars, whileStmt.posOpt.get, reporter)
                  for (p <- modObjectVars.entries) {
                    val (res, (tipe, pos)) = p
                    val (srw1, sym) = srw.freshSym(tipe, pos)
                    val srw2 = Util.assumeValueInv(logika, smt2, cache, rtCheck, srw1, sym, pos, reporter)
                    srw = srw2.addClaim(State.Claim.Let.CurrentName(sym, res.owner :+ res.id, Some(pos)))
                  }
                  val (receiverModified, modLocalVars) = whileStmt.contract.modifiedLocalVars(logika.context.receiverLocalTypeOpt)
                  val receiverOpt: Option[State.Value.Sym] = if (receiverModified) {
                    val (srw3, sym) = Util.idIntro(whileStmt.posOpt.get, srw, logika.context.methodName, "this",
                      logika.context.receiverLocalTypeOpt.get._2, None())
                    srw = srw3
                    Some(sym)
                  } else {
                    None()
                  }
                  srw = Util.rewriteLocalVars(srw, modLocalVars.keys, whileStmt.posOpt, reporter)
                  for (p <- modLocalVars.entries) {
                    val (res, (tipe, pos)) = p
                    val (srw4, sym) = Util.idIntro(pos, srw, res.context, res.id, tipe, Some(pos))
                    srw = Util.assumeValueInv(logika, smt2, cache, rtCheck, srw4, sym, pos, reporter)
                  }
                  if (receiverModified) {
                    val srw6 = Util.evalAssignReceiver(whileStmt.contract.modifies, logika, logika, smt2, cache, rtCheck, srw,
                      Some(AST.Exp.This(AST.TypedAttr(whileStmt.posOpt, Some(receiverOpt.get.tipe)))), receiverOpt,
                      HashMap.empty, reporter)
                    val (srw7, sym) = Util.idIntro(whileStmt.posOpt.get, srw6, logika.context.methodName, "this",
                      logika.context.receiverLocalTypeOpt.get._2, None())
                    srw = Util.assumeValueInv(logika, smt2, cache, rtCheck, srw7, sym, sym.pos, reporter)
                  }
                  srw
                }

                val s2 = State(T, s0R.claims ++ (for (i <- s0.claims.size until s1.claims.size) yield s1.claims(i)), s0R.nextFresh)

                for (p <- logika.evalExp(split, smt2, cache, rtCheck, s2, whileStmt.cond, reporter)) {
                  val (s3, v) = p
                  if (s3.status) {
                    val pos = whileStmt.cond.posOpt.get
                    val (s4, cond) = logika.value2Sym(s3, v, pos)
                    val prop = State.Claim.Prop(T, cond)
                    val thenClaims = s4.claims :+ prop
                    val thenSat = smt2.sat(cache, T, logika.config.logVc, logika.config.logVcDirOpt,
                      s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, thenClaims, reporter)
                    var nextFresh: Z = s4.nextFresh

                    if (thenSat) {
                      // can satisfy the true branch of the loop condition,
                      // so now evaluate the loop loop body
                      for (s5 <- logika.evalStmts(split, smt2, cache, None(), rtCheck, s4(claims = thenClaims), whileStmt.body.stmts, reporter)) {
                        if (s5.status) {

                          val postLoopStates = logika.checkExps(split, smt2, cache, F, "Loop invariant", " at the end of while-loop",
                            s5, nonFlowInvariants, reporter)

                          for (s6 <- InfoFlowUtil.checkInfoFlowAgreements(
                            invariantFlows, flowInAgrees._2, loopPartitionsToCheck,
                            "Flow Loop Invariant at end of while-loop ",
                            logika, smt2, cache, reporter, postLoopStates)) {
                            if (nextFresh < s6.nextFresh) {
                              nextFresh = s6.nextFresh
                            }
                          }
                        } else {
                          if (nextFresh < s5.nextFresh) {
                            nextFresh = s5.nextFresh
                          }
                        }
                      }
                      // done evaluating the body of the while loop
                    }

                    // now check to see if false/else branch of loop condition holds.  Note we're returning
                    // a state based of s4 claims which only includes claims from the loop invariant -- ie
                    // we're assuming the loop invariant holds when the loop exits
                    val negProp = State.Claim.Prop(F, cond)
                    val _elseClaims = s4.claims :+ negProp

                    val elseClaims = _elseClaims

                    val elseSat = smt2.sat(cache, T, logika.config.logVc, logika.config.logVcDirOpt,
                      s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, elseClaims, reporter)

                    var state = State(status = elseSat, claims = elseClaims, nextFresh = nextFresh)

                    // now capture the current value of each channels' out agreements
                    state = recordLoopInvariantOutAgrees(state, invariantFlows, whileStmt.posOpt, reporter)

                    r = r :+ state
                  } else {
                    r = r :+ s3
                  }
                }
              } else {
                r = r :+ s0w
              }
            }
            return r
          }
          case invalid =>
            val topLevels = ops.ISZOps(invalid).filter((p: AST.Exp) => p.isInstanceOf[AST.Exp.InfoFlowInvariant])
            val nonTopLevels = ops.ISZOps(invalid).filter((p: AST.Exp) => !p.isInstanceOf[AST.Exp.InfoFlowInvariant])
            if(nonTopLevels.nonEmpty) {
              reporter.error(nonTopLevels(0).posOpt, name, "Flow loop invariants cannot (currently) be subexpressions")
            } else if (topLevels.size > 1) {
              reporter.error(topLevels(0).posOpt, name, "There (currently) can only be one flow loop invariant per loop, which can contain multiple Flows")
            } else {
              halt("Infeasible")
            }
            return ISZ(s0(status = F))
        }
      case _ => halt("Infeasible")
    }
  }
}

@datatype class InfoFlowClaimPlugin extends ClaimPlugin {
  @pure def name: String = {
    return "InfoFlow Claim Plugin"
  }

  @pure def canHandleExp(claim: State.Claim): B = {
    return F
  }

  @pure def handleExp(cs2es: Util.ClaimsToExps, claim: State.Claim): Option[Exp] = {
    halt("Infeasible")
  }

  @pure def canHandleDeclSmt2(claim: State.Claim): B = {
    return F
  }

  @pure def canHandleSmt2(rhs: B, claim: State.Claim): B = {
    return F
  }

  @pure def handleDeclSmt2(smt2: Smt2, claim: State.Claim): ISZ[(String, ST)] = {
    halt("Infeasible")
  }

  @pure def handleSmt2(smt2: Smt2, claim: State.Claim, v2st: State.Value => ST, lets: HashMap[Z, ISZ[Claim.Let]], declIds: HashSMap[(ISZ[String], String, Z), Let.Id]): Option[ST] = {
    halt("Infeasible")
  }

  @pure def canHandleSymRewrite(data: Claim.Data): B = {
    data match {
      case i: InfoFlowContext.InfoFlowAgreeSym => return T
      case _ => return F
    }
  }

  @pure def handleSymRewrite(rw: Util.SymAddRewriter, data: Claim.Data): MOption[Claim.Data] = {
    data match {
      case i: InfoFlowContext.InfoFlowAgreeSym => return MSome(i(sym = rw.transformStateValueSym(i.sym).get))
      case _ => halt("Infeasible")
    }
  }
}
