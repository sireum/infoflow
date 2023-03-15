// #Sireum
package org.sireum.logika.infoflow

import org.sireum._
import org.sireum.lang.ast.MethodContract
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
         exp <- infoFlow.flowCase.outAgrees) {
      val (s1, r) = InfoFlowUtil.intro(exp, s, logika, smt2, cache, reporter)
      s = s1.addClaim(State.Claim.Custom(InfoFlowAgreeSym(r, infoFlow.flowCase.label.value)))
    }
    return s
  }

  def intro(exp: AST.Exp, state: State,
            logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter): (State, State.Value.Sym) = {
    val pos = exp.posOpt.get
    logika.singleStateValue(pos, state, logika.evalExp(Split.Disabled, smt2, cache, F, state, exp, reporter)) match {
      case (s, v: State.Value.Sym) => return (s, v)
      case (s, v) =>
        val (s1, sym) = s.freshSym(v.tipe, pos)
        return (s1.addClaim(State.Claim.Let.Def(sym, v)), sym)
    }
  }


  def captureAgreementValues(infoFlows: InfoFlowsType, captureInAgreements: B,
                             logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter, state: State): (State, AssumeContextType) = {
    var s = state
    var assumeContexts: AssumeContextType = HashMap.empty

    assert(s.status != State.Status.End, "How did we reach the return statement if we haven't processed the in agreements yet")

    for (infoFlow <- infoFlows.values if s.ok) {
      var reqSyms: ISZ[State.Value.Sym] = ISZ()
      if (captureInAgreements) {
        for (req <- infoFlow.flowCase.requires) {
          val (s1, r) = intro(req, s, logika, smt2, cache, reporter)
          s = s1
          reqSyms = reqSyms :+ r
        }
      }

      var inSyms: ISZ[State.Value.Sym] = ISZ()
      val agreements: ISZ[AST.Exp] = if (captureInAgreements) infoFlow.flowCase.inAgrees else infoFlow.flowCase.outAgrees
      for (inExp <- agreements) {
        val (s1, r) = intro(inExp, s, logika, smt2, cache, reporter)
        s = s1
        inSyms = inSyms :+ r
      }

      assumeContexts = assumeContexts + (infoFlow.flowCase.label.value ~> AssumeContext(reqSyms, inSyms))
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
        val channel = flowCheck.channel
        val flowContext = flowContexts.get(channel).get
        val outAgrees = flowCheck.exps
        val pos: Position = if (flowCheck.optPos.nonEmpty) flowCheck.optPos.get else altPos

        for (state <- states) {
          if (state.status == State.Status.Error) {
            r = r :+ state
          } else {
            assert(state.status == State.Status.Normal || state.status == State.Status.End, s"Not expecting ${state.status}")

            // if the method has a return statement then Logika will have already called checkMethodPost
            // and therefore the state's status will either be End or Normal.  If the former then
            // subsequent evalExp's (e.g. when intro'ing the out agreements) will result in
            // errors since the state status is not Normal/'ok'.  Workaround is to switch the state
            // back to 'ok' -- note we're throwing away 's' after checking its flows.
            var s: State = if (state.ok) state else state(status = State.Status.Normal)

            val inAgreementsFromClaims: AssumeContext =
              InfoFlowContext.getClaimAgreementSyms(s).get(channel) match {
                case Some(claimSyms) =>
                  assert(claimSyms.requirementSyms.isEmpty && claimSyms.inAgreementSyms.nonEmpty)
                  claimSyms
                case _ => AssumeContext(ISZ(), ISZ())
              }

            val implicationAgreements = InfoFlowContext.getImplicationAgreements(s)

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

            for (implication <- implicationAgreements) {
              val lhs = implication.lhs
              val rhs = implication.rhs

              val secondTraceLhs = lhs.map((sym: State.Value.Sym) => sym(num = sym.num + lastSymNum))
              val secondTraceRhs = rhs.map((sym: State.Value.Sym) => sym(num = sym.num + lastSymNum))

              assert(lhs.size == 1 && rhs.size == 1, "TODO")

              val (s1, sym1) = s.freshSym(AST.Typed.b, pos)
              s = s1
              val claim1 = State.Claim.Let.Binary(sym1, lhs(0), AST.Exp.BinaryOp.Eq, secondTraceLhs(0), lhs(0).tipe)
              s = s.addClaim(claim1)

              val (s2, sym2) = s.freshSym(AST.Typed.b, pos)
              s = s2
              val claim2 = State.Claim.Let.Binary(sym2, rhs(0), AST.Exp.BinaryOp.Eq, secondTraceRhs(0), rhs(0).tipe)
              s = s.addClaim(claim2)

              val (s3, sym3) = s.freshSym(AST.Typed.b, pos)
              s = s3
              val claim3 = State.Claim.Let.Binary(sym3, sym1, AST.Exp.BinaryOp.Imply, sym2, sym1.tipe)
              s = s.addClaim(claim3)

              s = s.addClaim(State.Claim.Prop(T, sym3))
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


            val kind: String = flowCheck.kind match {
              case FlowKind.Case => "flow case"
              case FlowKind.Flow => "flow"
              case FlowKind.Group => "flow group"
            }

            val validity = smt2.valid(context = logika.context.methodName, cache = cache, reportQuery = T,
              log = logika.config.logVc, logDirOpt = logika.config.logVcDirOpt,
              title = s"${title}$kind $channel at [${pos.beginLine}, ${pos.endLine}]", pos = pos,
              premises = s.claims, conclusion = conclusion, reporter = reporter)
            var ok = F
            validity.kind match {
              case Smt2Query.Result.Kind.Unsat => ok = T
              case Smt2Query.Result.Kind.Sat => logika.error(Some(pos), s"${title}$kind $channel violation", reporter)
              case Smt2Query.Result.Kind.Unknown => logika.error(Some(pos), s"${title}Could not verify $kind $channel", reporter)
              case Smt2Query.Result.Kind.Timeout => logika.error(Some(pos), s"${title}Timed out while checking $kind $channel", reporter)
              case Smt2Query.Result.Kind.Error => logika.error(Some(pos), s"${title}Error encountered when checking $kind $channel\n${validity.info}", reporter)
            }

            r = r :+ (if (ok) state else state(status = State.Status.Error))
          }
        }
      }
      return r
    } else {
      return states
    }
  }

  def translateToFlowCase(infoFlow: MethodContract.InfoFlowFlow): MethodContract.InfoFlowCase = {
    return MethodContract.InfoFlowCase(
      label = infoFlow.label,
      requiresClause = MethodContract.Claims.empty,
      inAgreeClause = infoFlow.fromClause,
      outAgreeClause = infoFlow.toClause)
  }

  def translateToFlows(infoFlow: MethodContract.InfoFlowGroup,
                       reads: ISZ[AST.Exp.Ref],
                       modifies: ISZ[AST.Exp.Ref]): MethodContract.InfoFlowFlow = {
    var fromClause = MethodContract.Claims.empty
    var toClause = MethodContract.Claims.empty
    if (reads.nonEmpty && modifies.nonEmpty) {
      var froms = ISZ[AST.Exp]()
      var tos = ISZ[AST.Exp]()

      val r = ops.ISZOps(reads)
      val m = ops.ISZOps(modifies)
      for (member <- infoFlow.members) {
        member match {
          case ref: AST.Exp.Ref =>
            if (r.contains(ref)) {
              froms = froms :+ member
            }
            if (m.contains(ref)) {
              tos = tos :+ member
            }
          case _ =>
        }
      }
      fromClause = MethodContract.Claims(claims = froms, attr = infoFlow.membersClause.attr)
      toClause = MethodContract.Claims(claims = tos, attr = infoFlow.membersClause.attr)
    } else {
      fromClause = infoFlow.membersClause
      toClause = infoFlow.membersClause
    }
    return MethodContract.InfoFlowFlow(
      label = infoFlow.label,
      fromClause = fromClause,
      toClause = toClause
    )
  }
}
