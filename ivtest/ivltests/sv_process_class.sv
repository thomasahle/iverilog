// Test the process class stub functionality
// Tests process::self(), status(), and await() methods
//
// Note: This tests the stub implementation in uvm_pkg.sv
// The await() method is a no-op and status() returns RUNNING

`include "uvm_pkg.sv"

module test;
  import uvm_pkg::*;

  process p1;
  process_state st;

  initial begin
    // Test process::self() returns a non-null handle
    p1 = process::self();
    if (p1 == null) begin
      $display("FAILED: process::self() returned null");
      $finish;
    end
    $display("Got process handle from self()");

    // Test status() returns a valid state
    st = p1.status();
    if (st != RUNNING) begin
      $display("FAILED: Expected RUNNING state, got %s", st.name());
      $finish;
    end
    $display("Process status: %s", st.name());

    // Test await() doesn't crash (it's a no-op)
    p1.await();
    $display("await() completed (no-op stub)");

    $display("PASSED");
    $finish;
  end
endmodule
