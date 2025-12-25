// Comprehensive SVA test combining multiple features
// Tests properties, sequences, implications, delays, first_match

module test;
  logic clk, reset;
  logic req, gnt, data_valid, data_ready;
  logic [7:0] data;

  //--------------------------------------------------
  // Sequence declarations
  //--------------------------------------------------
  
  // Simple sequence
  sequence s_req_high;
    @(posedge clk) req;
  endsequence : s_req_high

  // Sequence with port
  sequence s_signal_check(logic sig);
    @(posedge clk) sig == 1'b1;
  endsequence : s_signal_check

  // Sequence with multiple ports
  sequence s_handshake(logic valid, logic ready);
    @(posedge clk) valid && ready;
  endsequence : s_handshake

  //--------------------------------------------------
  // Property declarations
  //--------------------------------------------------
  
  // Request-grant property with fixed delay
  property p_req_gnt;
    @(posedge clk) disable iff(reset)
    req |-> ##[1:3] gnt;
  endproperty : p_req_gnt

  // Data valid implies data non-zero
  property p_valid_data(logic [7:0] d, logic v);
    @(posedge clk) disable iff(reset)
    v |-> (d != 8'h00);
  endproperty : p_valid_data

  // Handshake protocol
  property p_handshake;
    @(posedge clk) disable iff(reset)
    data_valid |-> ##[0:10] data_ready;
  endproperty : p_handshake

  // Chained implications
  property p_protocol;
    @(posedge clk) disable iff(reset)
    req |=> gnt |-> ##1 data_valid |=> data_ready;
  endproperty : p_protocol

  // Property with first_match
  property p_eventual_grant;
    @(posedge clk) disable iff(reset)
    req |-> first_match((##[1:100] gnt));
  endproperty : p_eventual_grant

  //--------------------------------------------------
  // Assertions and covers
  //--------------------------------------------------
  
  REQ_GNT_CHK: assert property (p_req_gnt);
  REQ_GNT_COV: cover property (p_req_gnt);
  
  VALID_DATA_CHK: assert property (p_valid_data(data, data_valid));
  
  HANDSHAKE_CHK: assert property (p_handshake);
  HANDSHAKE_COV: cover property (p_handshake);
  
  PROTOCOL_CHK: assert property (p_protocol);
  
  EVENTUAL_GNT: assert property (p_eventual_grant);

  // Inline assertions
  INLINE1: assert property (@(posedge clk) req |-> ##1 gnt);
  INLINE2: cover property (@(posedge clk) data_valid |=> data_ready);

  initial begin
    $display("PASSED - Comprehensive SVA test parsed successfully");
    $finish;
  end
endmodule
