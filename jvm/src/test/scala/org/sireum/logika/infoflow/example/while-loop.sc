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
        InAgree(a_in),
        OutAgree(a_out)
        /* Two Steps:
         *   1) Record the initial value of a_in after the requires statement is evaluated
         *   2) After evaluating method body, make 2nd copy, assert the initial a_in's are in
         *      agreement and show/prove we have agreement on the a_out's
         */
      ),
      Flow("b",
        InAgree(b_in),
        OutAgree(b_out))
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
         Flow("a",
           InAgree(a_acc, a_in),
           OutAgree(a_acc)
           /* Three Steps:
            *   1) beginning of while loop: add agreements for anything we've learned about 'a' up to this point and
            *      then show we have agreement on a_acc -- in this case we only know stuff about a_in
            *   2) through the loop: record the initial values of a_acc and a_in at the start of the loop,
            *      eval the loop body, and then show we have agreement on a_acc
            *   3) loop exit: add a_acc to 'a' channel's InAgree
            */
         ),
         Flow("b",
           InAgree(b_acc, b_in),
           OutAgree(b_acc)
         )
      )
    )
    a_acc = a_acc + a_in
    b_acc = b_acc + b_in
    i = i - 1
  }
  // record value of a_acc here and add a_acc to 'a' channel's in agreements (do similar thing for 'b')
  a_out = a_acc
  b_out = b_acc

  assert(T)
}
