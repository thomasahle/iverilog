// Test parameterized interface instantiation
// This tests that interfaces can have parameters like modules do

interface data_if #(parameter int WIDTH = 8);
  logic [WIDTH-1:0] data;
  logic valid;
  logic ready;

  modport master(output data, output valid, input ready);
  modport slave(input data, input valid, output ready);
endinterface

module producer #(parameter int W = 8) (data_if.master port);
  initial begin
    port.data = {W{1'b1}};
    port.valid = 1;
  end
endmodule

module consumer #(parameter int W = 8) (data_if.slave port);
  initial begin
    port.ready = 1;
    #1;
    if (port.data == {W{1'b1}} && port.valid == 1) begin
      $display("PASSED: Received correct data width %0d", W);
    end else begin
      $display("FAILED: Data mismatch");
    end
  end
endmodule

module test;
  // Instantiate interface with parameter
  data_if #(16) wide_bus();
  data_if #(8) narrow_bus();
  data_if default_bus();  // Uses default WIDTH=8

  producer #(16) prod16(.port(wide_bus));
  consumer #(16) cons16(.port(wide_bus));

  producer #(8) prod8(.port(narrow_bus));
  consumer #(8) cons8(.port(narrow_bus));

  producer #(8) prod_def(.port(default_bus));
  consumer #(8) cons_def(.port(default_bus));

  initial begin
    #10;
    $finish;
  end
endmodule
