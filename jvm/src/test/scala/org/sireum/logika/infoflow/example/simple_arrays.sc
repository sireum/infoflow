// #Sireum #Logika

import org.sireum._

val s1: MSZ[Z] = MSZ(0,1,2)

val s2: MSZ[Z] = MSZ(10,11,12)

def simpleArrays(): Unit = {
  Contract(
    Requires(s1.size == 3, s2.size == 3),
    Modifies(s1),
    // Note that it would be ideal if the Modifies cause could have the same level of precision as the infoflow.
    // If some variable cell is not modified, it doesn't need to appear in the output clause of a dependency.
    // If a variable cell does appear in the modifies clause, it should appear in the out clause of a dependency.
    InfoFlows(
      // general case that does not reference individual elements.
      // s1 depends on s2 for its 0'th element, but the rest of s1 for its other values.
      // Thus we need Flow(In(s1,s2), Out(s1))
      FlowCase("imprecise_array", // checks correctly
        InAgree(s1,s2),
        OutAgree(s1)
      ),
      FlowCase("precise_array_1",
        InAgree(s2),
        OutAgree(s1(0))
      ),
      FlowCase("precise_array_2",
        InAgree(s2(0),s2(1),s2(2)),
        OutAgree(s1(0))
      ),
      FlowCase("precise_array_3",
        InAgree(s1(1)),
        OutAgree(s1(1))
      )
    )
  )
  s1(0) = s2(0) + s2(1) + s2(2)
  assert(T)
}
