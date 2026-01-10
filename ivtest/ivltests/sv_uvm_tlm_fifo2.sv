// Test TLM FIFO improvements - bounded vs unbounded modes
`include "uvm_pkg.sv"
import uvm_pkg::*;

class my_item extends uvm_object;
  int value;
  function new(string name = "item");
    super.new(name);
  endfunction
endclass

class fifo_test extends uvm_test;
  uvm_tlm_fifo#(my_item) bounded_fifo;
  uvm_tlm_fifo#(my_item) unbounded_fifo;
  my_item item;
  bit ok;
  int passed = 0;
  int failed = 0;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    // Create bounded fifo with size 3
    bounded_fifo = new("bounded_fifo", this, 3);
    // Create unbounded fifo (size 0 = unbounded)
    unbounded_fifo = new("unbounded_fifo", this, 0);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    
    // Test 1: Bounded FIFO should accept up to bound items
    $display("Test 1: Bounded FIFO accepts items up to bound");
    for (int i = 0; i < 3; i++) begin
      item = new($sformatf("item%0d", i));
      item.value = i * 10;
      ok = bounded_fifo.try_put(item);
      if (!ok) begin
        $display("FAILED: Bounded FIFO should accept item %0d", i);
        failed++;
      end
    end
    if (bounded_fifo.size() == 3) begin
      $display("PASSED: Bounded FIFO has 3 items");
      passed++;
    end else begin
      $display("FAILED: Bounded FIFO has %0d items (expected 3)", bounded_fifo.size());
      failed++;
    end
    
    // Test 2: Bounded FIFO should reject items when full
    $display("Test 2: Bounded FIFO rejects items when full");
    item = new("overflow_item");
    item.value = 999;
    ok = bounded_fifo.try_put(item);
    if (!ok) begin
      $display("PASSED: Bounded FIFO correctly rejected 4th item");
      passed++;
    end else begin
      $display("FAILED: Bounded FIFO should have rejected 4th item");
      failed++;
    end
    
    // Test 3: Unbounded FIFO should accept many items
    $display("Test 3: Unbounded FIFO accepts many items");
    for (int i = 0; i < 100; i++) begin
      item = new($sformatf("item%0d", i));
      item.value = i;
      ok = unbounded_fifo.try_put(item);
      if (!ok) begin
        $display("FAILED: Unbounded FIFO rejected item %0d", i);
        failed++;
      end
    end
    if (unbounded_fifo.size() == 100) begin
      $display("PASSED: Unbounded FIFO has 100 items");
      passed++;
    end else begin
      $display("FAILED: Unbounded FIFO has %0d items (expected 100)", unbounded_fifo.size());
      failed++;
    end
    
    // Test 4: Get items from bounded FIFO in FIFO order
    $display("Test 4: Get items in FIFO order");
    for (int i = 0; i < 3; i++) begin
      bounded_fifo.get(item);
      if (item.value != i * 10) begin
        $display("FAILED: Expected %0d, got %0d", i * 10, item.value);
        failed++;
      end
    end
    if (bounded_fifo.size() == 0) begin
      $display("PASSED: Bounded FIFO is empty after gets");
      passed++;
    end
    
    // Test 5: Flush unbounded FIFO
    $display("Test 5: Flush FIFO");
    unbounded_fifo.flush();
    if (unbounded_fifo.size() == 0) begin
      $display("PASSED: Unbounded FIFO flushed");
      passed++;
    end else begin
      $display("FAILED: Unbounded FIFO has %0d items after flush", unbounded_fifo.size());
      failed++;
    end
    
    // Summary
    $display("----------------------------------------");
    if (failed == 0) begin
      $display("PASSED: All %0d tests passed", passed);
    end else begin
      $display("FAILED: %0d/%0d tests failed", failed, passed + failed);
    end
    
    phase.drop_objection(this);
  endtask
endclass

module test;
  initial begin
    run_test("fifo_test");
  end
endmodule
