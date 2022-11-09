// #Sireum
package org.sireum.logika.infoflow

import org.sireum._
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.{Reporter, Split}
import org.sireum.logika.State.Claim
import org.sireum.logika.State.Claim.Let
import org.sireum.logika.infoflow.InfoFlowContext.{FlowCheckType, FlowContext, FlowContextType, InfoFlowsType}
import org.sireum.logika.{Logika, Smt2, Smt2Query, State, StateTransformer, Util}

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

  def intro(exp: AST.Exp, state: State,
            logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter): (State, State.Value.Sym) = {
    exp match {
      case ref: AST.Exp.Ref =>
        val res = ref.resOpt.get
        res match {
          case lv: AST.ResolvedInfo.LocalVar =>
            return Util.idIntro(ref.posOpt.get, state, lv.context, s"${lv.id}", ref.typedOpt.get, None())
          case x => halt(s"Need to handle $x")
        }
      case x =>
        val split = Split.Disabled
        val rtCheck = F
        val (s1, r) = logika.singleStateValue(logika.evalExp(split, smt2, cache, rtCheck, state, exp, reporter))
        r match {
          case sym: State.Value.Sym =>
            return (s1, sym)
          case _ => halt(s"Unexpected value: $r")
        }
    }
  }


  def processInfoFlowInAgrees(infoFlows: InfoFlowsType,
                              logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter, state: State): (State, FlowContextType) = {
    var s = state
    var flowContexts: FlowContextType = HashSMap.empty

    for (infoFlow <- infoFlows.values if s.status) {
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
        flowContexts = flowContexts + (infoFlow.label.value ~> FlowContext(reqSyms, inSyms))
      }
    }
    return (s, flowContexts)
  }

  def checkInfoFlowAgreements(infoFlows: InfoFlowsType,
                              flowContexts: FlowContextType,
                              flowChecks: ISZ[FlowCheckType],
                              title: String,
                              logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter, states: ISZ[State]): ISZ[State] = {

    if (flowContexts.nonEmpty) {
      //assert(infoFlows.size == inAgreeSyms.size, s"${infoFlows.size} vs ${inAgreeSyms.size}")

      var r: ISZ[State] = ISZ()
      for (flowCheck <- flowChecks) {
        val channel = flowCheck._1
        val flowContext = flowContexts.get(channel).get
        val outAgrees = flowCheck._3
        val pos = flowCheck._2.get // TODO: possible this is empty

        for (state <- states) {
          if (!state.status) {
            r = r :+ state
          } else {
            var s = state

            val inAgreementsFromClaims: FlowContext =
              InfoFlowContext.getClaimAgreementSyms(s).get(channel) match {
                case Some(claimSyms) =>
                  assert(claimSyms.requirementSyms.isEmpty && claimSyms.inAgreementSyms.nonEmpty)
                  claimSyms
                case _ => FlowContext(ISZ(), ISZ())
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

            r = r :+ state(status = ok)
          }
        }
      }
      return r
    } else {
      return states
    }
  }
}
