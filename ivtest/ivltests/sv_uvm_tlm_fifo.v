// Test uvm_tlm_analysis_fifo basic functionality
// Tests instantiation, write, and size methods

`include "uvm_pkg.sv"

import uvm_pkg::*;

// Simple transaction class
class my_trans extends uvm_object;
  int value;

  function new(string name = "my_trans");
    super.new(name);
    value = 0;
  endfunction

  virtual function string get_type_name();
    return "my_trans";
  endfunction
endclass

module test;
  initial begin
    uvm_tlm_analysis_fifo #(my_trans) fifo;
    my_trans tx1, tx2;

    // Create FIFO
    fifo = new("test_fifo", null);

    // Create transactions
    tx1 = new("tx1"); tx1.value = 100;
    tx2 = new("tx2"); tx2.value = 200;

    // Test 1: Check FIFO is initially empty
    if (!fifo.is_empty()) begin
      $display("FAILED: FIFO should be empty initially");
      $finish;
    end
    if (fifo.size() != 0) begin
      $display("FAILED: FIFO size should be 0, got %0d", fifo.size());
      $finish;
    end

    // Test 2: Write items to FIFO
    fifo.write(tx1);
    if (fifo.size() != 1) begin
      $display("FAILED: FIFO size should be 1 after first write, got %0d", fifo.size());
      $finish;
    end

    fifo.write(tx2);
    if (fifo.size() != 2) begin
      $display("FAILED: FIFO size should be 2 after second write, got %0d", fifo.size());
      $finish;
    end

    // Test 3: FIFO should not be empty now
    if (fifo.is_empty()) begin
      $display("FAILED: FIFO should not be empty after writes");
      $finish;
    end

    // Test 4: used() should return same as size()
    if (fifo.used() != fifo.size()) begin
      $display("FAILED: used() = %0d should equal size() = %0d", fifo.used(), fifo.size());
      $finish;
    end

    // Test 5: flush() should empty the FIFO
    fifo.flush();
    if (!fifo.is_empty()) begin
      $display("FAILED: FIFO should be empty after flush");
      $finish;
    end
    if (fifo.size() != 0) begin
      $display("FAILED: FIFO size should be 0 after flush, got %0d", fifo.size());
      $finish;
    end

    $display("PASSED");
  end
endmodule
