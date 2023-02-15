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
      Flow("m1 a",
        From(a),
        To(a)),
      Flow("m1 b",
        From(b),
        To(b))
    )
  )
  a = a + 1
  b = b + 1
}

def context4(): Unit = {
  Contract(
    Modifies(a, b),
    InfoFlows(
      Flow("context-a",
        From(a, b),
        To(a)),
      Flow("context-b",
        From(b, x),
        To(b))
    )
  )

  a = a + b

  m1()

  b = b + x

  assert(T)
}
