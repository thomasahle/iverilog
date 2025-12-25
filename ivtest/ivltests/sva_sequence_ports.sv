// Test SVA sequence declarations with ports
// IEEE 1800-2012 Section 16.9

module test;
  logic clk, x, y, z;

  // Sequence with single port
  sequence s_single_port(logic sig);
    @(posedge clk) sig;
  endsequence : s_single_port

  // Sequence with multiple ports
  sequence s_multi_port(logic a, logic b);
    @(posedge clk) a && b;
  endsequence : s_multi_port

  // Sequence with typed ports
  sequence s_typed_port(bit [7:0] data, logic valid);
    @(posedge clk) valid && (data != 8'h00);
  endsequence : s_typed_port

  initial begin
    $display("PASSED - SVA sequences with ports parsed successfully");
    $finish;
  end
endmodule
