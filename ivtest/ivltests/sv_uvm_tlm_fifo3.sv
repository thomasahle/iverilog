// Test uvm_tlm_analysis_fifo with various operations
// Tests boundary conditions and multiple write/flush cycles

`include "uvm_pkg.sv"

module test;
  import uvm_pkg::*;

  uvm_tlm_analysis_fifo#(int) fifo;
  int i;

  initial begin
    fifo = new("int_fifo", null);

    // Test initial state
    if (fifo.size() != 0) begin
      $display("FAILED: Initial size should be 0");
      $finish;
    end

    // Write many values
    for (i = 0; i < 10; i++) begin
      fifo.write(i * 100);
    end

    if (fifo.size() != 10) begin
      $display("FAILED: After 10 writes, size should be 10, got %0d", fifo.size());
      $finish;
    end

    if (fifo.used() != 10) begin
      $display("FAILED: used() should be 10, got %0d", fifo.used());
      $finish;
    end

    if (fifo.is_empty()) begin
      $display("FAILED: FIFO should not be empty");
      $finish;
    end

    // Test flush
    fifo.flush();

    if (fifo.size() != 0) begin
      $display("FAILED: After flush, size should be 0");
      $finish;
    end

    if (!fifo.is_empty()) begin
      $display("FAILED: After flush, FIFO should be empty");
      $finish;
    end

    // Write again after flush
    fifo.write(999);
    if (fifo.size() != 1) begin
      $display("FAILED: After re-write, size should be 1");
      $finish;
    end

    // Multiple flush/write cycles
    fifo.flush();
    fifo.write(1);
    fifo.write(2);
    fifo.flush();
    fifo.write(3);

    if (fifo.size() != 1) begin
      $display("FAILED: After multiple cycles, size should be 1, got %0d", fifo.size());
      $finish;
    end

    $display("PASSED");
  end
endmodule
