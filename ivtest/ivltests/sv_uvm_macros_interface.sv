// Test UVM macros work in interfaces (not just classes)
// The macros should use %m format specifier to get hierarchical path

`include "uvm_macros.svh"

// Simple interface that uses UVM macros
interface simple_bfm;
  import uvm_pkg::*;

  logic [7:0] data;
  logic valid;

  // Task that uses uvm_info macro
  task drive(input logic [7:0] d);
    `uvm_info("BFM", $sformatf("Driving data: %h", d), UVM_LOW)
    data = d;
    valid = 1;
    #10;
    valid = 0;
  endtask

  // Initial block using uvm_info
  initial begin
    data = 0;
    valid = 0;
    `uvm_info("BFM", "Interface initialized", UVM_LOW)
  end
endinterface

module test;
  simple_bfm bfm();

  initial begin
    #5;
    bfm.drive(8'hAB);
    #20;

    // Verify the data was driven
    if (bfm.data == 8'hAB) begin
      $display("PASSED");
    end else begin
      $display("FAILED: data = %h, expected AB", bfm.data);
    end
    $finish;
  end
endmodule
