// Test uvm_test_done global instance
// Tests the set_drain_time() and get_drain_time() methods

`include "uvm_pkg.sv"

import uvm_pkg::*;

module test;
  initial begin
    time drain_time;

    // Check initial drain time is 0
    drain_time = uvm_test_done.get_drain_time();
    if (drain_time != 0) begin
      $display("FAILED: initial drain_time = %0t, expected 0", drain_time);
      $finish;
    end

    // Set drain time
    uvm_test_done.set_drain_time(null, 100ns);

    // Check drain time was set
    drain_time = uvm_test_done.get_drain_time();
    if (drain_time != 100ns) begin
      $display("FAILED: drain_time = %0t, expected 100ns", drain_time);
      $finish;
    end

    // Set a different drain time
    uvm_test_done.set_drain_time(null, 500ns);
    drain_time = uvm_test_done.get_drain_time();
    if (drain_time != 500ns) begin
      $display("FAILED: drain_time = %0t, expected 500ns", drain_time);
      $finish;
    end

    $display("PASSED");
  end
endmodule
