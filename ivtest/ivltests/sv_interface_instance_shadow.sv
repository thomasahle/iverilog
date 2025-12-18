// Test: Interface instance member access when interface is also used as port argument
// This tests the case where an interface instance is passed to a submodule as a port,
// and the same interface instance members are accessed directly in the parent module.
// This was previously failing because the port connection created a wire that shadowed
// the interface scope.

interface simple_if(input clk, input rst_n);
  logic [1:0] pselx;
  logic [7:0] data;
endinterface

module submod(simple_if intf);
  // Submodule accesses interface through port
  always @(posedge intf.pselx[0])
    $display("submod saw pselx[0] toggle");
endmodule

module test;
  bit clk;
  bit rst_n;

  // Interface instance
  simple_if intf(clk, rst_n);

  // Connect to submodule - this creates a wire that may shadow the interface scope
  submod sub_h(intf);

  // Access interface member in always_comb (r-value access)
  always_comb begin
    if (intf.pselx == 2'b01)
      $display("pselx is 01");
    else if (intf.pselx == 2'b10)
      $display("pselx is 10");
  end

  initial begin
    // L-value access to interface member after port connection
    intf.pselx = 2'b01;
    intf.data = 8'hAB;
    #1;

    // Verify the values were set correctly (r-value access)
    if (intf.pselx !== 2'b01) begin
      $display("FAILED: pselx = %b, expected 01", intf.pselx);
      $finish;
    end
    if (intf.data !== 8'hAB) begin
      $display("FAILED: data = %h, expected AB", intf.data);
      $finish;
    end

    // Change values
    intf.pselx = 2'b10;
    intf.data = 8'hCD;
    #1;

    if (intf.pselx !== 2'b10) begin
      $display("FAILED: pselx = %b, expected 10", intf.pselx);
      $finish;
    end
    if (intf.data !== 8'hCD) begin
      $display("FAILED: data = %h, expected CD", intf.data);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
