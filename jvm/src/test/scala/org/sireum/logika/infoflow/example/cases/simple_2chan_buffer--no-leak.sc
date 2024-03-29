// #Sireum #Logika

import org.sireum._

var a_in: Z = 0
var a_out: Z = 0
var b_in: Z = 0
var b_out: Z = 0

var c_out: Z = 0

def simple_2chan_buffer__no_leak(): Unit = {
  Contract(
    Modifies(a_out, b_out),
    InfoFlows(
      FlowCase("a_indOf_b",
        InAgree(a_in),
        OutAgree(a_out)),
      FlowCase("b_indOf_a",
        InAgree(b_in),
        OutAgree(b_out)))
  )
  a_out = a_in
  b_out = b_in
  assert(T)
}
