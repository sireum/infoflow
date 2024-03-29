// #Sireum #Logika
import org.sireum._

var in : Z = 0
var acc : B = T
var pin : Z = 0

def control_dependence__limited_release__with_leak(): Unit = {
  Contract(
    Modifies(acc),
    InfoFlows(
      Flow("limited release",
        From(in == pin),
        To(acc)))
  )
  if (in == pin) {
    acc = T
  } else {
    acc = F
  }

  if (pin > 0) { // << leak
    acc = F
  }

  assert(T)
}