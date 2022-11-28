// #Sireum
package org.sireum.logika.infoflow

import org.sireum._
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.{Reporter, Split}
import org.sireum.logika.State.Claim
import org.sireum.logika.State.Claim.Let
import org.sireum.logika.infoflow.InfoFlowContext._
import org.sireum.logika.{Logika, Smt2, Smt2Query, State, StateTransformer}
import org.sireum.message.Position

object InfoFlowUtil {

  val secondTraceSuffix: String = "~"

  @datatype class SymValueRewriter(val lastSymNum: Z) extends StateTransformer.PrePost[Z] {
    override def preStateValueSym(maxSym: Z,
                                  o: State.Value.Sym): StateTransformer.PreResult[Z, State.Value] = {
      val r = o.num + lastSymNum
      val _maxSym: Z = if (r > maxSym) r else maxSym

      return StateTransformer.PreResult(_maxSym, T, Some(o(num = r)))
    }

    override def preStateClaimLetCurrentId(ctx: Z, o: Let.CurrentId): StateTransformer.PreResult[Z, Claim.Let] = {
      return StateTransformer.PreResult(ctx, T, Some(o(id = s"${o.id}${secondTraceSuffix}")))
    }

    override def preStateClaimLetId(ctx: Z, o: Let.Id): StateTransformer.PreResult[Z, Claim.Let] = {
      return StateTransformer.PreResult(ctx, T, Some(o(id = s"${o.id}${secondTraceSuffix}")))
    }
  }


  def addInAgreeClaims(flowContext: AssumeContextType, state: State): State = {
    var s = state
    for (entry <- flowContext.entries;
         sym <- entry._2.requirementSyms ++ entry._2.inAgreementSyms) {
      s = s.addClaim(State.Claim.Custom(InfoFlowAgreeSym(sym, entry._1)))
    }
    return s
  }

  def addOutAgreeClaims(state: State, invariantFlows: InfoFlowsType,
                        logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter): State = {
    var s = state
    for (infoFlow <- invariantFlows.values;
         exp <- infoFlow.outAgrees) {
      val (s1, r) = InfoFlowUtil.intro(exp, s, logika, smt2, cache, reporter)
      s = s1.addClaim(State.Claim.Custom(InfoFlowAgreeSym(r, infoFlow.label.value)))
    }
    return s
  }

  def intro(exp: AST.Exp, state: State,
            logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter): (State, State.Value.Sym) = {
    logika.singleStateValue(logika.evalExp(Split.Disabled, smt2, cache, F, state, exp, reporter)) match {
      case (s, v: State.Value.Sym) => return (s, v)
      case (s, v) =>
        val (s1, sym) = s.freshSym(v.tipe, exp.posOpt.get)
        return (s1.addClaim(State.Claim.Let.Def(sym, v)), sym)
    }
  }


  def processInfoFlowInAgrees(infoFlows: InfoFlowsType,
                              logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter, state: State): (State, AssumeContextType) = {
    var s = state
    var assumeContexts: AssumeContextType = HashMap.empty

    for (infoFlow <- infoFlows.values if s.ok) {
      var reqSyms: ISZ[State.Value.Sym] = ISZ()
      for (req <- infoFlow.requires) {
        val (s1, r) = intro(req, s, logika, smt2, cache, reporter)
        s = s1
        reqSyms = reqSyms :+ r
      }

      var inSyms: ISZ[State.Value.Sym] = ISZ()
      for (inExp <- infoFlow.inAgrees) {
        val (s1, r) = intro(inExp, s, logika, smt2, cache, reporter)
        s = s1
        inSyms = inSyms :+ r
      }

      if (reqSyms.nonEmpty || inSyms.nonEmpty) {
        assumeContexts = assumeContexts + (infoFlow.label.value ~> AssumeContext(reqSyms, inSyms))
      }
    }
    return (s, assumeContexts)
  }

  def checkInfoFlowAgreements(flowContexts: AssumeContextType,
                              flowChecks: ISZ[FlowCheckType],
                              title: String,
                              altPos: Position,
                              logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter, states: ISZ[State]): ISZ[State] = {

    if (flowContexts.nonEmpty) {
      var r: ISZ[State] = ISZ()
      for (flowCheck <- flowChecks) {
        val channel = flowCheck._1
        val flowContext = flowContexts.get(channel).get
        val outAgrees = flowCheck._3
        val pos: Position = if (flowCheck._2.nonEmpty) flowCheck._2.get else altPos

        for (state <- states) {
          if (!state.ok) {
            r = r :+ state
          } else {
            var s = state

            val inAgreementsFromClaims: AssumeContext =
              InfoFlowContext.getClaimAgreementSyms(s).get(channel) match {
                case Some(claimSyms) =>
                  assert(claimSyms.requirementSyms.isEmpty && claimSyms.inAgreementSyms.nonEmpty)
                  claimSyms
                case _ => AssumeContext(ISZ(), ISZ())
              }

            // introduce sym value for the outAgrees
            var outSyms: ISZ[State.Value.Sym] = ISZ()
            for (outExp <- outAgrees) {
              val (s1, r) = intro(outExp, s, logika, smt2, cache, reporter)
              s = s1
              outSyms = outSyms :+ r
            }

            val lastSymNum = s.nextFresh - 1

            // create 2nd trace
            {
              val rewriter = StateTransformer[Z](SymValueRewriter(lastSymNum))
              val result = rewriter.transformState(lastSymNum, s)

              val secondTraceClaims = result.resultOpt.get.claims
              s = s(claims = s.claims ++ secondTraceClaims, nextFresh = result.ctx + 1)
            }

            // add requirement claims
            for (reqSym <- flowContext.requirementSyms) {
              val secInSym = reqSym(num = reqSym.num + lastSymNum)
              // assert both expressions eval to T in their respective traces
              s = s.addClaim(State.Claim.Prop(T, reqSym))
              s = s.addClaim(State.Claim.Prop(T, secInSym))
            }

            // add in agreements claims
            for (inSym <- flowContext.inAgreementSyms ++ inAgreementsFromClaims.inAgreementSyms) {
              val secInSym = inSym(num = inSym.num + lastSymNum)
              s = s.addClaim(State.Claim.Eq(inSym, secInSym))
            }

            // add out agreements claims
            var bstack: Stack[State.Value.Sym] = Stack.empty
            for (outSym <- outSyms) {
              val (s1, sym) = s.freshSym(AST.Typed.b, pos)
              s = s1
              bstack = bstack.push(sym)

              val secOutSym = outSym(num = outSym.num + lastSymNum)
              val claim = State.Claim.Let.Binary(sym, outSym, AST.Exp.BinaryOp.Eq, secOutSym, secOutSym.tipe)
              s = s.addClaim(claim)
            }

            while (bstack.size > 1) {
              val (sym1, _bstack) = bstack.pop.get
              val (sym2, __bsstack) = _bstack.pop.get
              bstack = __bsstack
              val (s1, sym3) = s.freshSym(AST.Typed.b, pos)
              bstack = bstack.push(sym3)
              s = s1
              val claim = State.Claim.Let.Binary(sym3, sym1, AST.Exp.BinaryOp.And, sym2, AST.Typed.b)
              s = s.addClaim(claim)
            }

            val sym = bstack.pop.get._1
            val conclusion = State.Claim.Prop(T, sym)

            val validity = smt2.valid(cache = cache, reportQuery = T, log = logika.config.logVc, logDirOpt = logika.config.logVcDirOpt,
              title = s"${title}Flow case $channel at [${pos.beginLine}, ${pos.endLine}]", pos = pos,
              premises = s.claims, conclusion = conclusion, reporter = reporter)

            var ok = F
            validity.kind match {
              case Smt2Query.Result.Kind.Unsat => ok = T
              case Smt2Query.Result.Kind.Sat => logika.error(Some(pos), s"${title}Flow case $channel violation", reporter)
              case Smt2Query.Result.Kind.Unknown => logika.error(Some(pos), s"${title}Could not verify flow case $channel", reporter)
              case Smt2Query.Result.Kind.Timeout => logika.error(Some(pos), s"${title}Timed out while checking flow case $channel", reporter)
              case Smt2Query.Result.Kind.Error => logika.error(Some(pos), s"${title}Error encountered when checking flow case $channel", reporter)
            }

            r = r :+ state(status = State.statusOf(ok))
          }
        }
      }
      return r
    } else {
      return states
    }
  }
}
