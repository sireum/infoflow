// #Sireum #Logika #InfoFlow

import org.sireum._

var a_in : Z = 0
var a_out : Z = 0
var b_in : Z = 0
var b_out: Z = 0

def while_loop(): Unit = {
  Contract(
    Requires((a_in > 0)),
    Modifies(a_out, b_out),
    InfoFlows(
      Flow("a",
        From(a_in),
        To(a_out)),
      Flow("b",
        From(b_in),
        To(b_out))
    )
  )

  var a_acc : Z = 0
  var b_acc : Z = 0

  var i : Z = 10

  while (i > 0) {
    Invariant(
      Modifies(a_acc, b_acc, i),
      i >= 0,
      InfoFlowInvariant(
         FlowCase("a",
           InAgree(a_acc, a_in),
           OutAgree(a_acc)
         ),
         FlowCase("b",
           InAgree(b_acc, b_in),
           OutAgree(b_acc)
         )
      )
    )
    a_acc = a_acc + a_in
    b_acc = b_acc + b_in
    i = i - 1
  }

  a_out = a_acc
  b_out = b_acc

  assert(T)
}
