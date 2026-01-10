// Test SVA property declarations with ports
// IEEE 1800-2012 Section 16.12

module test;
  logic clk, reset, x, y, z;

  // Property with single port
  property p_single_port(logic sig);
    @(posedge clk) disable iff(reset)
    sig;
  endproperty : p_single_port

  // Property with multiple ports
  property p_multi_port(logic a, logic b);
    @(posedge clk) disable iff(reset)
    a |-> b;
  endproperty : p_multi_port

  // Property with typed ports
  property p_typed_port(bit [7:0] data, logic valid);
    @(posedge clk) disable iff(reset)
    valid |-> data != 8'h00;  // No parens - workaround for LALR(1) conflict
  endproperty : p_typed_port

  // Assertions using properties with arguments (parsing only)
  CHECK1: assert property (p_single_port(x));
  CHECK2: assert property (p_multi_port(x, y));
  COVER1: cover property (p_single_port(z));

  initial begin
    $display("PASSED - SVA properties with ports parsed successfully");
    $finish;
  end
endmodule
