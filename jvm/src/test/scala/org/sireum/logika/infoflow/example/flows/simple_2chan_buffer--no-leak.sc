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
      Flow("a_indOf_b",
        From(a_in),
        To(a_out)),
      Flow("b_indOf_a",
        From(b_in),
        To(b_out)))
  )
  a_out = a_in
  b_out = b_in
  assert(T)
}
