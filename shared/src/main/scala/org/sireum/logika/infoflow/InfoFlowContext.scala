// #Sireum

package org.sireum.logika.infoflow

import org.sireum._
import org.sireum.lang.ast.MethodContract.InfoFlow
import org.sireum.lang.ast.Typed
import org.sireum.lang.{ast => AST}
import org.sireum.logika.State.Claim.Data
import org.sireum.logika.{Context, Logika, State, StateTransformer, Util}
import org.sireum.message.Position

object InfoFlowContext {

  type Channel = String

  val IN_AGREE_KEY: String = "IN_AGREE_KEY"

  @datatype class AssumeContext(val requirementSyms: ISZ[State.Value.Sym],
                                val inAgreementSyms: ISZ[State.Value.Sym])

  type AssumeContextType = HashMap[Channel, AssumeContext]

  val INFO_FLOWS_KEY: String = "INFO_FLOWS_KEY"
  type InfoFlowsType = HashMap[Channel, InfoFlow]

  type LogikaStore = HashMap[String, Context.Value]

  type FlowCheckType = (Channel, Option[Position], ISZ[AST.Exp])

  @datatype class InfoFlowAgreeSym(val sym: State.Value.Sym,
                                   val channel: String) extends Data {
    @pure def toRawST: ST = {
      halt("stub")
    }

    def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[State.Claim.Let]]): Unit = {}

    @pure def types: ISZ[Typed] = {
      return ISZ()
    }
  }

  @datatype class InAgreementValue(val inAgreements: AssumeContextType) extends Context.Value

  @datatype class InfoFlowsValue(val infoFlows: InfoFlowsType) extends Context.Value

  type SClaimAgree = ISZ[InfoFlowAgreeSym]

  @datatype class CollectAgreementSyms() extends StateTransformer.PrePost[SClaimAgree] {

    override
    def preStateClaimCustom(ctx: SClaimAgree,
                            o: State.Claim.Custom): StateTransformer.PreResult[SClaimAgree, State.Claim] = {
      o match {
        case State.Claim.Custom(i: InfoFlowAgreeSym) =>
          return StateTransformer.PreResult(ctx :+ i, T, None())
        case _ =>
          return StateTransformer.PreResult(ctx, T, None())
      }
    }
  }

  def getClaimAgreementSyms(state: State): AssumeContextType = {
    var ret: AssumeContextType = HashMap.empty
    val agreementClaims = StateTransformer[SClaimAgree](InfoFlowContext.CollectAgreementSyms()).transformState(ISZ(), state).ctx
    for (claim <- agreementClaims) {
      val inAgreeSyms: ISZ[State.Value.Sym] =
        if (ret.contains(claim.channel)) ret.get(claim.channel).get.inAgreementSyms
        else ISZ()
      ret = ret + claim.channel ~> AssumeContext(ISZ(), inAgreeSyms :+ claim.sym)
    }
    return ret
  }

  def putInAgreementsL(inAgreements: AssumeContextType, logika: Logika): Logika = {
    return logika(context = logika.context(storage = putInAgreements(inAgreements, logika.context.storage)))
  }

  def putInAgreements(inAgreements: AssumeContextType, store: LogikaStore): LogikaStore = {
    getInAgreements(store) match {
      case Some(existingMap) =>
        var mergedMap = existingMap
        for (entry <- inAgreements.entries if mergedMap.contains(entry._1)) {
          val mergedReqSyms = mergedMap.get(entry._1).get.requirementSyms ++ entry._2.requirementSyms
          val mergedInAgreements = mergedMap.get(entry._1).get.inAgreementSyms ++ entry._2.inAgreementSyms
          mergedMap = mergedMap + entry._1 ~> AssumeContext(mergedReqSyms, mergedInAgreements)
        }
        return store + IN_AGREE_KEY ~> InAgreementValue(mergedMap)
      case _ => return store + IN_AGREE_KEY ~> InAgreementValue(inAgreements)
    }
  }

  def getInAgreements(store: LogikaStore): Option[AssumeContextType] = {
    val ret: Option[AssumeContextType] = store.get(IN_AGREE_KEY) match {
      case Some(InAgreementValue(v)) => return Some(v)
      case _ => return None()
    }
    return ret
  }

  def putInfoFlowsL(infoFlows: InfoFlowsType, logika: Logika): Logika = {
    return logika(context = logika.context(storage = putInfoFlows(infoFlows, logika.context.storage)))
  }

  def putInfoFlows(infoFlows: InfoFlowsType, context: LogikaStore): LogikaStore = {
    return context + INFO_FLOWS_KEY ~> InfoFlowsValue(infoFlows)
  }

  def getInfoFlows(storage: LogikaStore): Option[InfoFlowsType] = {
    val ret: Option[InfoFlowsType] = storage.get(INFO_FLOWS_KEY) match {
      case Some(InfoFlowsValue(v)) => Some(v)
      case _ => None()
    }
    return ret
  }
}