package org.sireum.logika.infoflow

import org.sireum._
import org.sireum.test._
import org.sireum.logika.LogikaTest._
import org.sireum.logika.{Logika, LogikaTest, Smt2, Smt2Impl, Smt2Invoke}


object LogikaInfoFlowTests {
  val failSuffix: Predef.String = "-FAIL"
  val simplifiedPrefix: Predef.String = " (simplified)"
}

import LogikaInfoFlowTests._

class LogikaInfoFlowTests extends SireumRcSpec {

  def shouldIgnore(name: Predef.String): B = {
    //!ops.StringOps(name).contains("FlowGroup-FAIL")
    false
  }

  val root = Os.path(".") / "infoflow" / "jvm" / "src" / "test" / "scala" / "org" / "sireum" / "logika" / "infoflow"

  def textResources: scala.collection.Map[scala.Vector[Predef.String], Predef.String] = {
    ((Os.env("__CFBundleIdentifier"), Os.env("USER"))) match {
      case (Some(ive), Some(user)) if ive == string"com.jetbrains.intellij.ce" && user == string"belt" =>
        val root = Os.path(".") / "infoflow" / "jvm" / "src" / "test" / "scala" / "org" / "sireum" / "logika" / "infoflow"
        val p = root / "LogikaInfoFlowTests.scala"
        if (p.exists) { // force macro expansion when in IVE
          val content = ops.StringOps(p.read)
          p.writeOver(if (content.endsWith(" ")) content.substring(0, content.size - 1) else s"${p.read} ")
        }
      case _ =>
    }
    val m = $internal.RC.text(Vector("example")) { (p, f) => !p.last.endsWith("while-loop--FAIL.sc") }
    implicit val ordering: Ordering[Vector[Predef.String]] = m.ordering
    for ((k, v) <- m if !shouldIgnore(k.last);
         pair <- Seq((k, v), (k.dropRight(1) :+ s"${k.last}$simplifiedPrefix", v))) yield pair
  }

  val logPc: B = F
  val logRawPc: B = F
  val logVc: B = F
  var logVcDirOpt: Option[String] = None()

  def check(path: scala.Vector[Predef.String], content: Predef.String): scala.Boolean = {
    Smt2Invoke.haltOnError = T
    val isSimplified = path.last.endsWith(simplifiedPrefix)
    val p = if (isSimplified) path.dropRight(1) :+ path.last.replace(simplifiedPrefix, "") else path
    val reporter = logika.ReporterImpl.create(config.logPc, config.logRawPc, config.logVc, config.detailedInfo)
    var c = config(simplifiedQuery = isSimplified)
    val f = Os.path(p.mkString(Os.fileSep.value))

    if (logVc) {
      val d = root / "example" / s"vcs_${(ops.StringOps(p.last).substring(0, p.last.length - 3))}" / path.last
      logVcDirOpt = Some(d.string)
      if (d.exists) {
        d.removeAll()
      }
    }

    c = c(logPc = logPc, logRawPc = logRawPc, logVc = logVc, logVcDirOpt = logVcDirOpt)
    val nameExePathMap = Smt2Invoke.nameExePathMap(sireumHome)
    Logika.checkScript(Some(f.string), content, c, nameExePathMap, Os.numOfProcessors, th => Smt2Impl.create(c, ISZ(),
      th, reporter), logika.NoTransitionSmt2Cache.create, reporter, T, Logika.defaultPlugins ++
        InfoFlowPlugins.defaultPlugins, 0, ISZ(), ISZ())
    reporter.printMessages()
    val name = f.name.value
    if (name.contains(failSuffix)) {
      reporter.messages.elements.filter(m => !m.isInfo).exists(m => m.text.value.contains("Flow") && m.text.value.contains("violation"))
    } else {
      !reporter.hasIssue
    }
  }
} 