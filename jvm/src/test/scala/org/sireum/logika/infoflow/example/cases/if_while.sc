// #Sireum #Logika

import org.sireum._

var num: Z = 0

var s: Z = 0

var result: Z = 0

var b_in: Z = 0
var b_acc: Z = 0

def if_while(): Unit = {
  Contract(
    Modifies(result, num),
    InfoFlows(
      FlowCase("num",
        InAgree(num, s),
        OutAgree(result)
      )
    )
  )

  if(s > 0) {
    // multiply
    var num_accMult: Z = num
    //num = b_in
    var counter: Z = s
    //Deduce( |- (AssertAgree("num", OutAgree(num_accMult, num))))
    while(counter > 0) {
      Invariant(
        Modifies(num_accMult, counter),
        InfoFlowInvariant(
          FlowCase("num",
            InAgree(num_accMult, num),
            OutAgree(num_accMult)
          )
        )
      )
      num_accMult = num_accMult + num
      counter = counter - 1
    }
    // record value of num_accMult and add it to num's in agreeements
    result = num_accMult
    assert(T)
  } else {
    // divide
    var num_accDiv: Z = num
    var counter: Z = s
    while(counter < 0) {
      Invariant(
        Modifies(num_accDiv, counter),
        InfoFlowInvariant(
          FlowCase("num",
            InAgree(num_accDiv, num),
            OutAgree(num_accDiv)
          )
        )
      )
      num_accDiv = num_accDiv - num
      counter = counter + 1
    }
    // record value of num_accDiv and add it to num's in agreeements
    result = num_accDiv
    assert(T)
  }

  assert(T)
}