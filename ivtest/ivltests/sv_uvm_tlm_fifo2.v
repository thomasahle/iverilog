// Test uvm_tlm_analysis_fifo with multiple write operations
// Tests write, size, is_empty, used, and flush methods

`include "uvm_pkg.sv"

module test;
  import uvm_pkg::*;

  uvm_tlm_analysis_fifo#(int) fifo;

  initial begin
    fifo = new("test_fifo", null);

    // Test initial state
    if (fifo.size() != 0) begin
      $display("FAILED: Initial size should be 0, got %0d", fifo.size());
      $finish;
    end

    if (!fifo.is_empty()) begin
      $display("FAILED: Initial FIFO should be empty");
      $finish;
    end

    // Write multiple values
    fifo.write(10);
    fifo.write(20);
    fifo.write(30);

    if (fifo.size() != 3) begin
      $display("FAILED: After 3 writes, size should be 3, got %0d", fifo.size());
      $finish;
    end

    if (fifo.is_empty()) begin
      $display("FAILED: FIFO should not be empty after writes");
      $finish;
    end

    if (fifo.used() != 3) begin
      $display("FAILED: used() should return 3, got %0d", fifo.used());
      $finish;
    end

    // Test flush
    fifo.flush();

    if (fifo.size() != 0) begin
      $display("FAILED: After flush, size should be 0, got %0d", fifo.size());
      $finish;
    end

    if (!fifo.is_empty()) begin
      $display("FAILED: After flush, FIFO should be empty");
      $finish;
    end

    $display("PASSED");
  end
endmodule
