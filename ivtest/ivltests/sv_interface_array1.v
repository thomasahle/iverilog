// Test interface array instantiation
// IEEE 1800-2005: arrays of interface instances

interface simple_if(input logic clk);
  logic [7:0] data;
  logic valid;
endinterface

module test;
  logic clk;

  // Single interface instance
  simple_if single_intf(clk);

  // Array of interface instances with explicit size
  simple_if intf_arr[2](clk);

  // Array with range
  simple_if intf_range[0:1](clk);

  initial begin
    clk = 0;
    #1;

    // Access single interface
    single_intf.data = 8'hAA;
    single_intf.valid = 1;

    // Access array elements
    intf_arr[0].data = 8'hBB;
    intf_arr[0].valid = 1;
    intf_arr[1].data = 8'hCC;
    intf_arr[1].valid = 0;

    // Access range array
    intf_range[0].data = 8'hDD;
    intf_range[1].data = 8'hEE;

    #1;

    // Verify values
    if (single_intf.data !== 8'hAA) begin
      $display("FAILED: single_intf.data = %0h", single_intf.data);
      $finish;
    end

    if (intf_arr[0].data !== 8'hBB) begin
      $display("FAILED: intf_arr[0].data = %0h", intf_arr[0].data);
      $finish;
    end

    if (intf_arr[1].data !== 8'hCC) begin
      $display("FAILED: intf_arr[1].data = %0h", intf_arr[1].data);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
