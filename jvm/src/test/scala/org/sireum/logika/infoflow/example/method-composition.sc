// #Sireum #Logika

import org.sireum._

var a: Z = 0
var b: Z = 0
var x: Z = 0
var y: Z = 0

def m1(): Unit = {
  Contract(
    Modifies(a, b),
    InfoFlows(
      FlowCase("m1 a",
        InAgree(a),
        OutAgree(a)),
      FlowCase("m1 b",
        InAgree(b),
        OutAgree(b))
    )
  )
  a = a + 1
  b = b + 1
}

def context4(): Unit = {
  Contract(
    Modifies(a, b),
    InfoFlows(
      FlowCase("context-a",
        InAgree(a, b),
        OutAgree(a)),
      FlowCase("context-b",
        InAgree(b, x),
        OutAgree(b))
    )
  )

  a = a + b

  m1()

  b = b + x

  assert(T)
}
