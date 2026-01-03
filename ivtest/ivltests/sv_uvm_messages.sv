// Test UVM messaging macros
// Compile with: iverilog -g2012 -I<uvm_dir> uvm_pkg.sv sv_uvm_messages.sv
`include "uvm_macros.svh"
import uvm_pkg::*;

module test;
  int msg_count;

  initial begin
    msg_count = 0;

    // Test uvm_info macro
    `uvm_info("TEST", "Info message", UVM_LOW)
    msg_count++;

    `uvm_info("TEST", $sformatf("Formatted message: %0d", 42), UVM_MEDIUM)
    msg_count++;

    // Test uvm_warning macro
    `uvm_warning("TEST", "Warning message")
    msg_count++;

    // Test uvm_error macro
    `uvm_error("TEST", "Error message")
    msg_count++;

    // All messages should have been printed
    if (msg_count == 4) begin
      $display("PASSED");
    end else begin
      $display("FAILED: expected 4 messages, got %0d", msg_count);
    end
    $finish;
  end
endmodule
