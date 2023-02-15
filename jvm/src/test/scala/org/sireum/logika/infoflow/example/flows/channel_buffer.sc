// #Sireum #Logika

import org.sireum._
import org.sireum.N16._

// Creating a method with global return values for testing
// auto info flow verification.
var A_out_global: N16 = n16"0"
var B_out_global: N16 = n16"0"
def channel_buffer_noninterference(A_in: N16, B_in: N16): (N16, N16) = {
  Contract(
    Modifies(A_out_global, B_out_global),
    Ensures(A_in == Res[(N16, N16)]._1,
      B_in == Res[(N16, N16)]._2
    ),
    InfoFlows(
      Flow("aChan_integrity usingRes",
        From(A_in),
        To(Res[(N16, N16)]._1)),
      Flow("aChan_integrity using globals",
        From(A_in),
        To(A_out_global)),

      Flow("bChan_integrity using Res",
        From(B_in),
        To(Res[(N16, N16)]._2)),
      Flow("bChan_integrity using globals",
        From(B_in),
        To(B_out_global)))
  )
  A_out_global = A_in
  B_out_global = B_in
  return (A_out_global, B_out_global)
}








