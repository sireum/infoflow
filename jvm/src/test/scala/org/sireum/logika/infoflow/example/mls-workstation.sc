// #Sireum #Logika

//  This is example is based on challenge problem concept presented to KSU researchers
//  by engineers at the German company SecuNet around 2010.
//
//  The current code is an abstraction of key concepts of the example.  More detailed
//  versions will be incrementally developed.
import org.sireum._

var current_domain: Z = 0;  // security domain that is currently being seviced by the work station.

var keyboard_input: C = ' ';            // abstracts port receiving inputs (keystrokes) from physical keyboard
var domain_0_keyboard_input: C = ' ';   // abstracts port on domain 0 interface to which keystrokes are forwarded
var domain_1_keyboard_input: C = ' ';   //  (similar)
var domain_2_keyboard_input: C = ' ';   //  (similar)

val null_keyboard_value: C = 'Z' // indicates the absence of keyboard stroke information as input to domains

def serviceOneStep(): Unit = {
  Contract(
    Requires(0 <= current_domain && current_domain <= 2),
    Modifies(domain_0_keyboard_input, domain_1_keyboard_input, domain_2_keyboard_input),
    InfoFlows(
      FlowCase("unconditional_case", //
        // (for illustration purposes, only spec for domain0 is given
        //   similar cases would be given for domain1, domain2)
        // Technically I do not believe that null_keyboard_value needs to be
        //  listed in the InAgreements below because it is a "constant",
        //  and the implicit invariant on it should ensure that it never varies.
        // Therefore, I would expect the flow spec below to pass, but it
        // currently fails.
        // InAgree(keyboard_input, null_keyboard_value, current_domain),
        InAgree(keyboard_input, current_domain),
        OutAgree(domain_0_keyboard_input)),
      FlowCase("domain0_active",
        // "conditional" flow specification
        // Intuition:
        // Flow(In(keyboard_input),
        //      Out(domain_0_keyboard_input),
        //    When(current_domain == 0))
        Requires(current_domain == 0),
        InAgree(keyboard_input),
        OutAgree(domain_0_keyboard_input)),
      FlowCase("domain0_inactive",
        // "conditional" flow specification
        // Intuition: domain_0_keyboard_input does not depend
        //   on keyboard_input when its domain is not active.
        // Flow(In(),
        //      Out(domain_0_keyboard_input),
        //    When(current_domain != 0))
        Requires(current_domain != 0),
        //InAgree(null_keyboard_value), // shouldn't be needed
        InAgree(),
        OutAgree(domain_0_keyboard_input)),
      FlowCase("domain1_active",
        // "conditional" flow specification
        Requires(current_domain == 1),
        InAgree(keyboard_input),
        OutAgree(domain_1_keyboard_input)),
      FlowCase("domain1_inactive",
        // "conditional" flow specification
        // Intuition: domain_1_keyboard_input does not depend
        //   on keyboard_input when its domain is not active.
        // Flow(In(),
        //      Out(domain_1_keyboard_input),
        //    When(current_domain != 1))
        Requires(current_domain != 1),
        //InAgree(null_keyboard_value), // shouldn't be needed
        InAgree(),
        OutAgree(domain_1_keyboard_input)),
      FlowCase("domain2_active",
        // "conditional" flow specification
        Requires(current_domain == 2),
        InAgree(keyboard_input),
        OutAgree(domain_2_keyboard_input)),
      FlowCase("domain2_inactive",
        // "conditional" flow specification
        // Intuition: domain_2_keyboard_input does not depend
        //   on keyboard_input when its domain is not active.
        // Flow(In(),
        //      Out(domain_2_keyboard_input),
        //    When(current_domain != 2))
        Requires(current_domain != 2),
        //InAgree(null_keyboard_value), // shouldn't be needed
        InAgree(),
        OutAgree(domain_2_keyboard_input)),
    )
  )
  // ..would like the ability to mention specific variables/expressions in inline agreements

  Deduce(|- ( InlineAgree("unconditional_case", OutAgree(current_domain))),
  //       |- ( InlineAgree("unconditional_case") )
  )

  if (current_domain == 0) {
    domain_0_keyboard_input = keyboard_input;
    domain_1_keyboard_input = null_keyboard_value;
    domain_2_keyboard_input = null_keyboard_value;
  }

  assert(null_keyboard_value == 'Z')

  if (current_domain == 1) {
    domain_0_keyboard_input = null_keyboard_value;
    domain_1_keyboard_input = keyboard_input;
    domain_2_keyboard_input = null_keyboard_value;
  }

  if (current_domain == 2) {
    domain_0_keyboard_input = null_keyboard_value;
    domain_1_keyboard_input = null_keyboard_value;
    domain_2_keyboard_input = keyboard_input;
  }

  assert(T)
}

// Note:
//  For John to check:
//   Is there still a gap in the verification above:  Intuitively, we desire the flows to be
//   conditioned on the values of the ready flags in the pre-state.  We don't want to allow
//   those flags to be modified before the condition is checked to enable the flows.
