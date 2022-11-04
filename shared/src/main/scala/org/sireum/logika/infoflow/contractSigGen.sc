// #Sireum

import org.sireum._
import org.sireum.S64._

@sig trait Keyword
@datatype class S(v: String) extends Keyword
@datatype class P(v1: String, v2: String) extends Keyword

def genCombos(keywords: ISZ[Keyword]): ISZ[ISZ[Keyword]] = {

  val range = (s64"1" << conversions.Z.toS64(keywords.size)) - s64"1"

  var ret: ISZ[ISZ[Keyword]] = ISZ()
  for (i <- s64"0" to range) {
    var x = s64"0"
    var y = i
    var accum = ISZ[Keyword]()
    while (y > s64"0") {
      if ((y & s64"1") == s64"1") {
        accum = accum :+ keywords(conversions.S64.toZ(x))
      }
      x = x + s64"1"
      y = y >> s64"1"
    }
    ret = ret :+ accum
  }
  return ops.ISZOps(ret).sortWith((a, b) => a.size < b.size)
}

val k: ISZ[Keyword] = ISZ(S("Reads"), S("Requires"), S("Modifies"), S("Ensures"), S("InfoFlows"), P("Case", "Case*"))

var forObject = st""
var forOnly = st""

for(s <- genCombos(k) if ops.ISZOps(s).contains(S("InfoFlows"))) {
  var args: ISZ[ST] = ISZ()
  var args2: ISZ[ST] = ISZ()

  var suffix = ""
  for(i <- 0 until s.size) {
    s(i) match {
      case S(v) =>
        args = args :+ st"arg${i}: $v"
        args2 = args2 :+ st"${ops.StringOps(v).firstToLower}: $v"
      case P(v1, v2) =>
        args = args :+ st"arg${i}: $v1, arg${i + 1}: $v2"
        suffix = "S"
    }
  }
  forObject = st"""$forObject
                  |
                  |def apply(${(args, ", ")}): Unit = macro Macro.lUnit${s.size}${suffix}"""

  if(!ops.ISZOps(s).contains(P("Case", "Case*"))){
    forOnly = st"""$forOnly
                  |
                  |def apply[T](${(args2, ", ")}): T = ???"""
  }

  println(forObject.render)

  println(forOnly.render)
}