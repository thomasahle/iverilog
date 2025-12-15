// Test: parameterized interface instantiation
// This tests interface with parameter override

interface ParamIface #(parameter WIDTH = 8);
  logic [WIDTH-1:0] data;
  logic valid;
endinterface

module test;
  // Parameterized interface with different widths
  ParamIface #(16) wide_if();
  ParamIface #(4)  narrow_if();
  ParamIface #()   default_if();  // Uses default WIDTH=8

  initial begin
    wide_if.data = 16'hABCD;
    wide_if.valid = 1;
    narrow_if.data = 4'hF;
    narrow_if.valid = 1;
    default_if.data = 8'h55;
    default_if.valid = 1;

    #1;
    if (wide_if.data !== 16'hABCD) begin
      $display("FAILED: wide_if.data=%h expected ABCD", wide_if.data);
      $finish;
    end
    if (narrow_if.data !== 4'hF) begin
      $display("FAILED: narrow_if.data=%h expected F", narrow_if.data);
      $finish;
    end
    if (default_if.data !== 8'h55) begin
      $display("FAILED: default_if.data=%h expected 55", default_if.data);
      $finish;
    end
    $display("PASSED");
  end
endmodule
