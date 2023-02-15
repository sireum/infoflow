// #Sireum #Logika

//  For a detailed explanation of this example, see
//    Specification and Checking of Software Contracts for Conditional Information Flow
//    Authors: Torben Amtoft, John Hatcliff, Edwin Rodríguez, Robby, Jonathan Hoag, David Greve
//    Published in: FM 2008: Formal Methods

import org.sireum._

var in0_ready: B = true; // indicates data in in0 is fresh ("ready to read by mailbox")
var in0_data: C = ' ';
var out0_ready: B = true; // indicates data in in0 is fresh ("ready to read by client")
var out0_data: C = ' ';

var in1_ready: B = true;
var in1_data: C = ' ';
var out1_ready: B = true;
var out1_data: C = ' ';

def guardOneStep(): Unit = {
  Contract(
    Modifies(in0_ready, out1_ready, out1_data, in1_ready, out0_ready, out0_data),
    // Note: only one direction of the contracts are presented.
    //       The other direction is symmetric.
    InfoFlows(
      FlowCase("in0_to_out1 unconditional",
        InAgree(in0_data, out1_data, in0_ready, out1_ready),
        OutAgree(out1_data)),
      FlowCase("in0_to_out1_data_moves",
        Requires(in0_ready & !out1_ready),
        InAgree(in0_data, in0_ready, out1_ready),
        OutAgree(out1_data)),
      FlowCase("in0_to_out1_data_blocked",
        Requires(!in0_ready | out1_ready),
        InAgree(out1_data, in0_ready, out1_ready),
        OutAgree(out1_data)),
    )
  )
  var data0: C = ' ';
  var data1: C = ' ';
  out1_data = data0

  // move from in0 to out1 if data in in0 is fresh and data in out1 is stale (already by read by client)
  if (in0_ready & !out1_ready) {
    data0 = in0_data // read value from in0

    // uncomment to violate in0_to_out1_data_moves
    //data0 = in1_data

    in0_ready = false // mark in0 as empty (value has been consumed)
    // Future enhancement: insert call to filter here
    out1_data = data0 // move the in0 value into out1
    out1_ready = true // mark out1 as full (value has been placed into the buffer)
  } else {
    // uncomment to violate in0_to_out1_data_blocked
    //out1_data = in1_data
  }

  //  // move from in1 to out0
  //if (!in1_ready | out0_ready) {
  //  data1 = in0_data; // read value from in1
  //  in1_ready = false; // mark in1 as empty (value has been consumed)
  //  out0_data = data1; // move the in1 value into out0
  //  out0_ready = true; // mark out1 as full (value has been placed into the buffer)
  //}

  assert(T)
}

// Note:
//  For John to check:
//   Is there still a gap in the verification above:  Intuitively, we desire the flows to be
//   conditioned on the values of the ready flags in the pre-state.  We don't want to allow
//   those flags to be modified before the condition is checked to enable the flows.
