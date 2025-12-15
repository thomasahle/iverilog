// Test that interface port syntax is recognized and gives a clear error message
// Interface ports are not yet fully supported, but the parser recognizes them
// and gives a helpful error message.

interface TestIface;
  logic [7:0] data;
  logic clk;
endinterface

// This should give a clear "sorry: Interface port not yet supported" error
module test_module(TestIface iface_port);
  initial begin
    $display("PASSED");
  end
endmodule
