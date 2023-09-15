// #Sireum

package org.sireum.logika.infoflow

import org.sireum._
import org.sireum.lang.symbol.Info
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.{Reporter, Split}
import org.sireum.logika.infoflow.InfoFlowContext.{FlowElement, FlowKind, InfoFlowsType}
import org.sireum.logika.{Context, Logika, Smt2, State, Util}
import org.sireum.message.Position

object InfoFlowCompositional {

  def methodResST(res: AST.ResolvedInfo.Method): ST = {
    val owner: ISZ[String] =
      if (res.owner.size >= 2 && res.owner(0) == "org" && res.owner(1) == "sireum") ops.ISZOps(res.owner).drop(2)
      else res.owner
    return if (owner.isEmpty) st"${res.id}"
    else if (res.isInObject) st"${(owner, ".")}.${res.id}"
    else st"${(owner, ".")}#${res.id}"
  }

  def handleCompositional(logika: Logika,
                          smt2: Smt2,
                          cache: Logika.Cache,
                          rtCheck: B,
                          split: Split.Type,
                          posOpt: Option[message.Position],

                          info: Context.InvokeMethodInfo,
                          s: State,
                          typeSubstMap: HashMap[String, AST.Typed],
                          retType: AST.Typed,
                          invokeReceiverOpt: Option[AST.Exp],
                          receiverOpt: Option[State.Value.Sym],
                          paramArgs: ISZ[(AST.ResolvedInfo.LocalVar, AST.Typed, AST.Exp, State.Value)],
                          reporter: Reporter): ISZ[(State, State.Value)] = {
    val res = info.res
    val ctx = res.owner :+ res.id
    val pos = posOpt.get
    val resST = methodResST(res)
    val contract = info.contract
    val isUnit = info.sig.returnType.typedOpt == AST.Typed.unitOpt

    val (infoFlows, reads, modifies): (AST.MethodContract.InfoFlows, AST.MethodContract.Accesses, AST.MethodContract.Accesses) =
      contract match {
        case AST.MethodContract.Simple(reads, requires, modifies, ensures, flows, attr) => (flows, reads, modifies)
        case _ => (AST.MethodContract.InfoFlows.empty, AST.MethodContract.Accesses.empty, AST.MethodContract.Accesses.empty)
      }

    val receiverPosOpt: Option[Position] =
      if (invokeReceiverOpt.nonEmpty) invokeReceiverOpt.get.posOpt
      else info.sig.id.attr.posOpt
    val invs: ISZ[Info.Inv] =
      if (info.isHelper || info.strictPureBodyOpt.nonEmpty) ISZ()
      else logika.retrieveInvs(res.owner, res.isInObject)
    var r = ISZ[(State, State.Value)]()
    for (cm <- logika.context.compMethods if cm == ctx) {
      reporter.error(posOpt, Logika.kind, st"Cannot use ${(res.owner :+ res.id, ".")}'s contracts cyclicly".render)
      r = r :+ ((s(status = State.Status.Error), State.errorValue))
      return r
    }

    var s1 = s
    var oldVars = HashSMap.empty[String, State.Value.Sym]
    if (ctx == logika.context.methodName) {
      for (paramArg <- paramArgs) {
        val id = paramArg._1.id
        val (s2, sym) = Util.idIntro(pos, s1, ctx, paramArg._1.id, paramArg._4.tipe, None())
        oldVars = oldVars + id ~> sym
        s1 = s2
      }
      s1 = Util.rewriteLocals(s1, F, ctx, oldVars.keys ++ (if (receiverOpt.isEmpty) ISZ[String]() else ISZ[String]("this")))._1
    }
    for (q <- paramArgs) {
      val (l, _, arg, v) = q
      val argPosOpt = arg.posOpt
      val (s3, sym) = Util.idIntro(arg.posOpt.get, s1, l.context, l.id, v.tipe, argPosOpt)
      val (s4, vSym) = logika.value2Sym(s3, v, argPosOpt.get)
      s1 = s4.addClaim(State.Claim.Eq(sym, vSym))
    }

    val lComp: Logika = {
      val l = Util.logikaMethod(logika.context.nameExePathMap, logika.context.maxCores, logika.context.fileOptions,
        logika.th, logika.config, info.isHelper, res.owner, res.id, receiverOpt.map(t => t.tipe), info.sig.paramIdTypes,
        info.sig.returnType.typedOpt.get, receiverPosOpt, contract.reads, ISZ(), contract.modifies, ISZ(), ISZ(),
        logika.plugins, Some(
          (s"(${if (res.owner.isEmpty) "" else res.owner(res.owner.size - 1)}${if (res.isInObject) '.' else '#'}${res.id}) ",
            info.sig.id.attr.posOpt.get)),
        logika.context.compMethods :+ (res.owner :+ res.id)
      )
      val mctx = l.context.methodOpt.get
      var objectVarInMap = mctx.objectVarInMap
      for (p <- mctx.modObjectVarMap(typeSubstMap).entries) {
        val (ids, (t, _)) = p
        val (s4, sym) = Util.nameIntro(pos, s1, ids, t, None())
        objectVarInMap = objectVarInMap + ids ~> sym
        s1 = s4
      }
      var fieldVarInMap = mctx.fieldVarInMap
      mctx.receiverTypeOpt match {
        case Some(receiverType) =>
          val fieldVarMap = mctx.fieldVarMap(typeSubstMap)
          if (fieldVarMap.nonEmpty) {
            val (s5, thiz) = Util.idIntro(mctx.posOpt.get, s1, mctx.name, "this", receiverType, mctx.posOpt)
            s1 = s5
            for (p <- mctx.fieldVarMap(typeSubstMap).entries) {
              val (id, (t, posOpt)) = p
              val (s6, sym) = s1.freshSym(t, posOpt.get)
              s1 = s6.addClaim(State.Claim.Let.FieldLookup(sym, thiz, id))
              fieldVarInMap = fieldVarInMap + id ~> sym
            }
          }
        case _ =>
      }
      var localInMap = mctx.localInMap
      for (p <- mctx.localMap(typeSubstMap).entries) {
        val (id, (_, ctx, _, t)) = p
        val (s7, sym): (State, State.Value.Sym) = Util.idIntro(pos, s1, ctx, id, t, None())
        localInMap = localInMap + id ~> sym
        s1 = s7
      }
      l(context = l.context(methodOpt = Some(mctx(objectVarInMap = objectVarInMap, fieldVarInMap = fieldVarInMap,
        localInMap = localInMap))))
    }

    val (receiverModified, modLocals) = contract.modifiedLocalVars(lComp.context.receiverLocalTypeOpt, typeSubstMap)

    def evalContractCase(logikaComp: Logika, callerReceiverOpt: Option[State.Value.Sym], assume: B, cs0: State,
                         labelOpt: Option[AST.Exp.LitString], requires: ISZ[AST.Exp],
                         ensures: ISZ[AST.Exp]): Context.ContractCaseResult = {

      def modVarsResult(ms0: State, mposOpt: Option[Position]): (State, State.Value.Sym) = {
        var ms1 = ms0
        val modObjectVars = contract.modifiedObjectVars
        val mpos = mposOpt.get
        ms1 = Util.rewriteObjectVars(logikaComp, smt2, cache, rtCheck, ms1, modObjectVars, mpos, reporter)
        var oldIdMap = HashMap.empty[ISZ[String], State.Value.Sym]
        for (pair <- modLocals.entries) {
          val (info, (t, _)) = pair
          val (ls0, sym) = Util.idIntro(pos, ms1, info.context, info.id, t, None())
          ms1 = ls0
          oldIdMap = oldIdMap + (info.context :+ info.id) ~> sym
        }
        ms1 = Util.rewriteLocalVars(logikaComp, ms1, T, modLocals.keys, mposOpt, reporter)
        for (pair <- modLocals.entries) {
          val (info, (t, pos)) = pair
          val oldSym = oldIdMap.get(info.context :+ info.id).get
          val (ls1, newSym) = Util.idIntro(pos, ms1, info.context, info.id, t, Some(pos))
          val ls2 = Util.assumeValueInv(logika, smt2, cache, rtCheck, ls1, newSym, pos, reporter)
          if (AST.Util.isSeq(t)) {
            val (ls5, size1) = ls2.freshSym(AST.Typed.z, pos)
            val (ls6, size2) = ls5.freshSym(AST.Typed.z, pos)
            val (ls7, cond) = ls6.freshSym(AST.Typed.b, pos)
            val ls8 = ls7.addClaims(ISZ[State.Claim](
              State.Claim.Let.FieldLookup(size1, oldSym, "size"),
              State.Claim.Let.FieldLookup(size2, newSym, "size"),
              State.Claim.Let.Binary(cond, size2, AST.Exp.BinaryOp.Eq, size1, AST.Typed.z),
              State.Claim.Prop(T, cond)
            ))
            ms1 = ls8
          } else {
            ms1 = ls2
          }
        }
        if (isUnit) {
          return ms1.freshSym(AST.Typed.unit, mpos)
        } else {
          val (ms2, v) = Util.resIntro(mpos, ms1, ctx, retType, mposOpt)
          ms1 = ms2
          return (ms1, v)
        }
      }

      def modVarsRewrite(ms0: State, modPosOpt: Option[Position]): State = {
        var ms1 = ms0
        var newVars = oldVars
        for (q <- paramArgs) {
          val (p, t, arg, _) = q
          if (modLocals.contains(p)) {
            val (ms2, v) = Util.idIntro(arg.posOpt.get, ms1, p.context, p.id, t, None())
            ms1 = logika.singleState(logika.assignRec(Split.Disabled, smt2, cache, rtCheck, ms2, arg, v, reporter))
            if (newVars.contains(p.id)) {
              newVars = newVars + p.id ~> v
            }
          }
        }
        var rwLocals: ISZ[AST.ResolvedInfo.LocalVar] = for (q <- paramArgs) yield q._1
        if (!isUnit) {
          rwLocals = rwLocals :+ AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, T, T, "Res")
        }
        if (receiverOpt.nonEmpty) {
          rwLocals = rwLocals :+ AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, "this")
        }
        ms1 = Util.rewriteLocalVars(logikaComp, ms1, F, rwLocals, modPosOpt, reporter)
        if (newVars.nonEmpty) {
          for (q <- paramArgs) {
            val p = q._1
            newVars.get(p.id) match {
              case Some(v) => ms1 = ms1.addClaim(State.Claim.Let.CurrentId(T, v, ctx, p.id, posOpt))
              case _ =>
            }
          }
        }
        callerReceiverOpt match {
          case Some(receiver) =>
            val (ms2, receiverSym) = Util.idIntro(receiver.pos, ms1, logika.context.methodOpt.get.name, "this", receiver.tipe, Some(receiver.pos))
            ms1 = ms2.addClaim(State.Claim.Eq(receiverSym, receiver))
          case _ =>
        }
        return ms1
      }

      def evalRequires(cs1: State, label: String, rep: Reporter): (State, ISZ[State.Value]) = {
        var requireSyms = ISZ[State.Value]()
        var i = 0
        var csr0 = cs1
        for (require <- requires if csr0.ok) {
          val title: String =
            if (requires.size == 1) st"${label}re-condition of $resST".render
            else st"${label}re-condition#$i of $resST".render

          val (csr1, sym): (State, State.Value.Sym) =
            if (assume) {
              val p = logikaComp.evalAssume(smt2, cache, F, title, csr0, AST.Util.substExp(require, typeSubstMap), posOpt, rep)
              val size = p._1.claims.size
              assert(p._1.claims(size - 1) == State.Claim.Prop(T, p._2))
              (p._1(claims = ops.ISZOps(p._1.claims).slice(0, size - 1)), p._2)
            } else {
              logikaComp.evalAssert(smt2, cache, F, title, csr0, AST.Util.substExp(require, typeSubstMap), posOpt, ISZ(), rep)
            }
          requireSyms = requireSyms :+ sym
          csr0 = csr1
          i = i + 1
        }
        return (csr0, requireSyms)
      }

      def evalEnsures(cs1: State, label: String, rep: Reporter): State = {
        val claims: ISZ[AST.Exp] = for (ensure <- ensures) yield AST.Util.substExp(ensure, typeSubstMap)
        var i = 0
        var cse3 = cs1
        for (ensure <- claims if cse3.ok) {
          val title: String =
            if (ensures.size == 1) st"${label}ost-condition of $resST".render
            else st"${label}ost-condition#$i of $resST".render
          cse3 = logikaComp.evalAssume(smt2, cache, F, title, cse3, ensure, posOpt, rep)._1
          i = i + 1
        }
        return cse3
      }

      val rep = reporter.empty

      // eval the case label (why 'p'/'P')
      val (label, cs1): (String, State) = labelOpt match {
        case Some(lbl) if lbl.value.size == 0 =>
          (s"(${lbl.value}) p", cs0.addClaim(State.Claim.Label(lbl.value, lbl.posOpt.get)))
        case _ => ("P", cs0)
      }

      // eval requires
      val (cs2, requireSyms) = evalRequires(cs1, label, rep)
      if (!cs2.ok) {
        val (cs3, rsym) = cs2.freshSym(AST.Typed.b, pos)
        return Context.ContractCaseResult(F, cs3.addClaim(State.Claim.Let.And(rsym, requireSyms)),
          State.errorValue, State.Claim.Prop(T, rsym), rep.messages)
      }

      // capture in agreement values
      var inAgreements: InfoFlowsType = HashMap.empty[String, FlowElement]
      val pluginName = "Info Flow Compositional Plugin"
      for (infoFlowElem <- infoFlows.flows) {
        infoFlowElem match {
          case infoFlow: AST.MethodContract.InfoFlowCase =>
            if (inAgreements.contains(infoFlow.label.value)) {
              reporter.error(infoFlow.label.posOpt, pluginName, "Flow case channels must be unique")
            }

            assert(infoFlow.requires.isEmpty, "TODO")

            val modInfoFlow = infoFlow(inAgreeClause = infoFlow.inAgreeClause(claims = infoFlow.inAgrees.map((e: AST.Exp) => AST.Util.substExp(e, typeSubstMap))))
            inAgreements = inAgreements + infoFlow.label.value ~> FlowElement(modInfoFlow, FlowKind.Case)

          case infoFlow: AST.MethodContract.InfoFlowFlow =>
            val flowCase = InfoFlowUtil.translateToFlowCase(infoFlow)
            if (inAgreements.contains(flowCase.label.value)) {
              reporter.error(flowCase.label.posOpt, pluginName, "Flows channels must be unique")
            }
            inAgreements = inAgreements + flowCase.label.value ~> FlowElement(flowCase, FlowKind.Flow)

          case infoFlow: AST.MethodContract.InfoFlowGroup =>
            val flows = InfoFlowUtil.translateToFlows(infoFlow, reads.refs, modifies.refs)
            val flowCase = InfoFlowUtil.translateToFlowCase(flows)
            if (inAgreements.contains(flowCase.label.value)) {
              reporter.error(flowCase.label.posOpt, pluginName, "Group labels must be unique")
            }
            inAgreements = inAgreements + flowCase.label.value ~> FlowElement(flowCase, FlowKind.Group)
        }
      }
      val stateSyms = InfoFlowUtil.captureAgreementValues(inAgreements, T, logikaComp, smt2, cache, reporter, cs2)
      val cs3 = stateSyms._1

      // eval ensures
      val (cs4, result) = modVarsResult(cs3, posOpt)
      val cs5 = evalEnsures(cs4, label, rep)
      if (!cs5.ok) {
        val (cs6, rsym) = cs5.freshSym(AST.Typed.b, pos)
        return Context.ContractCaseResult(T, cs6.addClaim(State.Claim.Let.And(rsym, requireSyms)),
          State.errorValue, State.Claim.Prop(T, rsym), rep.messages)
      }

      val (cs10, rcvOpt): (State, Option[State.Value.Sym]) = if (receiverOpt.nonEmpty) {
        receiverOpt match {
          case Some(receiver) if invs.nonEmpty =>
            val (cs7, rcv) = Util.idIntro(pos, cs5, ctx, "this", receiver.tipe, None())
            if (isUnit) {
              (cs7, Some(rcv))
            } else {
              val (cs8, res) = Util.resIntro(pos, cs7, ctx, retType, None())
              val cs9 = Util.assumeValueInv(logikaComp, smt2, cache, rtCheck, cs8, res, pos, reporter)
              (cs9, Some(rcv))
            }
          case _ => (cs5, receiverOpt)
        }
      } else {
        (cs5, None())
      }

      val cs11 = Util.checkInvs(logikaComp, posOpt, T, "Post-invariant", smt2, cache, rtCheck, cs10,
        logikaComp.context.receiverTypeOpt, rcvOpt, invs, typeSubstMap, reporter)

      val cs12 = Util.evalAssignReceiver(
        if (receiverModified) contract.modifies else ISZ(), // modifies
        logika, logikaComp, smt2, cache, rtCheck, cs11, invokeReceiverOpt, receiverOpt, typeSubstMap, reporter)

      val cs13 = modVarsRewrite(cs12, posOpt)
      val (cs14, rsym) = cs13.freshSym(AST.Typed.b, pos)
      val cs15 = cs14.addClaim(State.Claim.Let.And(rsym, requireSyms))

      // capture out agreement values
      var outAgreements: InfoFlowsType = HashMap.empty[String, FlowElement]
      for (infoFlowElement <- infoFlows.flows) {
        infoFlowElement match {
          case infoFlowCase: AST.MethodContract.InfoFlowCase =>
            val modInfoFlow = infoFlowCase(outAgreeClause = infoFlowCase.outAgreeClause(claims = infoFlowCase.outAgrees.map((e: AST.Exp) => AST.Util.substExp(e, typeSubstMap))))
            outAgreements = outAgreements + infoFlowCase.label.value ~> FlowElement(modInfoFlow, FlowKind.Case)

          case infoFlow: AST.MethodContract.InfoFlowFlow =>
            val flowCase = InfoFlowUtil.translateToFlowCase(infoFlow)
            val modInfoFlow = flowCase(outAgreeClause = flowCase.outAgreeClause(claims = flowCase.outAgrees.map((e: AST.Exp) => AST.Util.substExp(e, typeSubstMap))))
            outAgreements = outAgreements + infoFlow.label.value ~> FlowElement(modInfoFlow, FlowKind.Flow)

          case infoFlowGroup: AST.MethodContract.InfoFlowGroup =>
            val flow = InfoFlowUtil.translateToFlows(infoFlowGroup, reads.refs, modifies.refs)
            val flowCase = InfoFlowUtil.translateToFlowCase(flow)
            val modInfoFlow = flowCase(outAgreeClause = flowCase.outAgreeClause(claims = flowCase.outAgrees.map((e: AST.Exp) => AST.Util.substExp(e, typeSubstMap))))
            outAgreements = outAgreements + flowCase.label.value ~> FlowElement(modInfoFlow, FlowKind.Flow)
        }
      }
      val outStateSyms = InfoFlowUtil.captureAgreementValues(outAgreements, F, logikaComp, smt2, cache, reporter, cs15)
      val cs16 = outStateSyms._1

      var csRet = cs16
      for (inEntry <- stateSyms._2.entries) {
        val outEntry = outStateSyms._2.get(inEntry._1).get
        val inSyms = inEntry._2.inAgreementSyms
        val outSyms = outEntry.inAgreementSyms
        val ifiaClaim = State.Claim.Custom(InfoFlowContext.InfoFlowImplicationAgree(lhs = inSyms, rhs = outSyms))
        csRet = csRet.addClaim(ifiaClaim)
      }

      return Context.ContractCaseResult(T, csRet, result, State.Claim.Prop(T, rsym), rep.messages)
    }

    val callerReceiverOpt: Option[State.Value.Sym] = logika.context.methodOpt match {
      case Some(m) => m.receiverTypeOpt match {
        case Some(currentReceiverType) =>
          val lcontext = logika.context.methodOpt.get.name
          val p = Util.idIntro(posOpt.get, s1, lcontext, "this", currentReceiverType, None())
          s1 = p._1
          if (receiverModified && logika.context.methodName == lcontext) {
            s1 = Util.rewriteLocal(logika, s1, F, lcontext, "this", posOpt, reporter)
          }
          Some(p._2)
        case _ => None()
      }
      case _ => None()
    }
    receiverOpt match {
      case Some(receiver) =>
        val (s2, receiverSym) = Util.idIntro(receiver.pos, s1, res.owner :+ res.id, "this", receiver.tipe, receiverPosOpt)
        s1 = s2.addClaim(State.Claim.Eq(receiverSym, receiver))
      case _ =>
    }
    s1 = {
      val pis = Util.checkInvs(lComp, posOpt, F, "Pre-invariant", smt2, cache, rtCheck, s1,
        lComp.context.receiverTypeOpt, receiverOpt, invs, typeSubstMap, reporter)
      s1(status = pis.status, nextFresh = pis.nextFresh)
    }
    contract match {
      case contract: AST.MethodContract.Simple if s1.ok =>
        val ccr = evalContractCase(lComp, callerReceiverOpt, F, s1, None(), contract.requires, contract.ensures)
        reporter.reports(ccr.messages)
        r = r :+ ((ccr.state, ccr.retVal))
      case contract: AST.MethodContract.Cases if s1.ok =>
        val root = s1
        var isPreOK = F
        var ccrs = ISZ[Context.ContractCaseResult]()
        var okCcrs = ISZ[Context.ContractCaseResult]()
        for (cas <- contract.cases) {
          val ccr = evalContractCase(lComp, callerReceiverOpt, T, s1,
            if (cas.label.value == "") None() else Some(cas.label), cas.requires, cas.ensures)
          ccrs = ccrs :+ ccr
          isPreOK = isPreOK || ccr.isPreOK
          if (ccr.isOK) {
            okCcrs = okCcrs :+ ccr
          }
          s1 = s1(nextFresh = ccr.state.nextFresh)
        }
        if (!isPreOK) {
          for (ccr <- ccrs) {
            reporter.reports(ccr.messages)
          }
        }
        if (!isPreOK || okCcrs.isEmpty) {
          r = r :+ ((s1(status = State.Status.Error), State.errorValue))
        } else if (okCcrs.size == 1) {
          val ccr = okCcrs(0)
          s1 = s1(claims = ccr.state.claims :+ ccr.requiresClaim)
          reporter.reports(ccr.messages)
          r = r :+ ((s1, ccr.retVal))
        } else {
          val shouldSplit: B = split match {
            case Split.Default => logika.config.splitAll || logika.config.splitContract
            case Split.Enabled => T
            case Split.Disabled => F
          }
          for (ccr <- okCcrs) {
            reporter.reports(ccr.messages)
          }
          var nextFresh: Z =
            ops.ISZOps(okCcrs).foldLeft((nf: Z, ccr: Context.ContractCaseResult) =>
              if (nf < ccr.state.nextFresh) ccr.state.nextFresh else nf, -1)
          assert(nextFresh >= 0)
          if (!isUnit) {
            nextFresh = nextFresh + 1
          }
          if (shouldSplit) {
            for (ccr <- okCcrs) {
              val cs = ccr.requiresClaim +:
                ops.ISZOps(ccr.state.claims).slice(root.claims.size, ccr.state.claims.size)
              val claims = ops.ISZOps(ccr.state.claims).slice(0, root.claims.size) ++ cs
              r = r :+ ((ccr.state(nextFresh = nextFresh, claims = claims), ccr.retVal))
            }
          } else {
            var claims = ISZ[State.Claim]()
            var map = HashMap.empty[State.Claim.Prop, ISZ[State.Claim]]
            for (i <- 0 until root.claims.size) {
              val rootClaim = root.claims(i)
              if (ops.ISZOps(okCcrs).forall((ccr: Context.ContractCaseResult) => ccr.state.claims(i) == rootClaim)) {
                claims = claims :+ rootClaim
              } else {
                for (ccr <- okCcrs) {
                  val l = map.get(ccr.requiresClaim).getOrElse(ISZ())
                  map = map + ccr.requiresClaim ~> (l :+ ccr.state.claims(i))
                }
              }
            }
            val implies: ISZ[State.Claim] = for (ccr <- okCcrs) yield State.Claim.Imply(T, ISZ(ccr.requiresClaim,
              Util.bigAnd(
                map.get(ccr.requiresClaim).getOrElse(ISZ()) ++
                  (for (i <- root.claims.size until ccr.state.claims.size) yield ccr.state.claims(i)))
            ))
            claims = claims ++ implies
            claims = claims :+ State.Claim.Or(for (ccr <- okCcrs) yield ccr.requiresClaim)
            s1 = s1(claims = claims)
            if (isUnit) {
              r = r :+ ((s1(nextFresh = nextFresh), okCcrs(0).retVal))
            } else {
              val (s8, sym) = s1.freshSym(retType, pos)
              s1 = s8
              r = r :+ ((s1(nextFresh = nextFresh).addClaims(
                for (ccr <- okCcrs) yield State.Claim.Imply(T, ISZ(ccr.requiresClaim,
                  State.Claim.Let.Def(sym, ccr.retVal)))), sym))
            }
          }
        }
      case _ => r = r :+ ((s1, State.errorValue))
    }
    val oldR = r
    r = ISZ()
    var nextFresh: Z = -1
    for (sv <- oldR) {
      val s9 = sv._1
      if (s9.nextFresh > nextFresh) {
        nextFresh = s9.nextFresh
      }
      r = r :+ sv
    }
    r = for (sv <- r) yield (sv._1(nextFresh = nextFresh), sv._2)
    return r
  }
}
