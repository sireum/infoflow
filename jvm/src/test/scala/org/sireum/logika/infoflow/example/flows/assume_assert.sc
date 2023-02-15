// #Sireum #Logika
import org.sireum._

var a_in: Z = 0
var a_out: Z = 0

var b_in: Z = 0
var b_out: Z = 0

var c_in: Z = 0
var c_out: Z = 0

def assume_assert(): Unit = {
  Contract(
    Modifies(a_out, b_out),
    InfoFlows(
      Flow("a",
        From(a_in),
        To(a_out)),
      Flow("b",
        From(b_in),
        To(b_out)
      )
    )
  )

  // comment out the following to get a violation of 'a'
  Deduce( |- ( AssumeAgree("a", InAgree(b_in))))

  a_out = a_in + b_in
  b_out = b_in

  assert(T)
}

def assume_assert2(): Unit = {
  Contract(
    Modifies(a_out, b_out),
    InfoFlows(
      Flow("a",
        From(a_in),
        To(a_out)),
      Flow("b",
        From(b_in),
        To(b_out)
      )
    )
  )

  a_out = a_in + b_out
  b_out = b_in

  // comment out the following for a violation of 'b'
  Deduce(|-(AssumeAgree("a", InAgree(In(b_out)))))

  assert(T)
}