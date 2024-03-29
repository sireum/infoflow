// #Sireum #Logika
import org.sireum._

var a_in : Z = 0
var a_out : Z = 0
var b_in : Z = 0
var b_out: Z = 0

def control_dependence_masked_leak_2(): Unit = {
  Contract(
    Modifies(b_out),
    InfoFlows(
      Flow("b_indOf_a",
        From(b_in),
        To(b_out)))
  )
  if (a_in > 0) {
    b_out = b_in + 1
  } else {
    b_out = b_in - 1
  }
  assert(T)
}
