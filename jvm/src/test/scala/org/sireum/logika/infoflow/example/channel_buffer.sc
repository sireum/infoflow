// #Sireum #Logika
import org.sireum._
import org.sireum.N16._


// Creating a method with global return values for testing
// auto info flow verification.
var A_out_global: N16 = n16"0"
var B_out_global: N16 = n16"0"
def channel_buffer_noninterference(A_in: N16, B_in: N16): (N16,N16) = {
  Contract(
    Modifies(A_out_global, B_out_global),
    Ensures(A_in == Res[(N16,N16)]._1,
      B_in == Res[(N16,N16)]._2
    ),
    // Tipe rejects the following as Res can only appear in Ensures clauses
    //    InfoFlows(
    //      FlowCase("aChan_integrity",
    //        InAgree(A_in),
    //        OutAgree(Res[(N16,N16)]._1)),
    //      FlowCase("bChan_integrity",
    //        InAgree(B_in),
    //        OutAgree(Res[(N16,N16)]._2)))
    // current workaround is to rewrite using globals
    InfoFlows(
      FlowCase("aChan_integrity",
        InAgree(A_in),
        OutAgree(A_out_global)),
      FlowCase("bChan_integrity",
        InAgree(B_in),
        OutAgree(B_out_global)))
  )
  A_out_global= A_in
  B_out_global = B_in
  return (A_out_global,B_out_global)
}








