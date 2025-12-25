// Test SVA unbounded delay ranges ##[m:$]
// IEEE 1800-2012 Section 16.9.2

module test;
  logic clk, reset;
  logic req, ack, done;

  // Property with unbounded delay in consequent
  property p_eventual_ack;
    @(posedge clk) disable iff(reset)
    req |-> ##[1:$] ack;
  endproperty : p_eventual_ack

  // Property with unbounded delay at start
  property p_eventually_done;
    @(posedge clk) disable iff(reset)
    ##[0:$] done;
  endproperty : p_eventually_done

  // Property with non-overlapping implication and unbounded delay
  property p_req_then_ack;
    @(posedge clk) disable iff(reset)
    req |=> ##[1:$] ack;
  endproperty : p_req_then_ack

  // Assertions using unbounded delays
  EVENTUAL_ACK: assert property (p_eventual_ack);
  EVENTUALLY_DONE: assert property (p_eventually_done);
  REQ_THEN_ACK: assert property (p_req_then_ack);

  // Cover properties with unbounded delays
  COV_ACK: cover property (@(posedge clk) req |-> ##[1:$] ack);
  COV_DONE: cover property (@(posedge clk) ##[0:$] done);

  initial begin
    $display("PASSED - SVA unbounded delay patterns parsed successfully");
    $finish;
  end
endmodule
