// Test for UVM factory type override
// This test verifies that factory type overrides work correctly.
// When the override is registered, $ivl_factory_create() should create
// the override type instead of the original type.

`include "uvm_pkg.sv"
`include "uvm_macros.svh"

import uvm_pkg::*;

// Base transaction class
class base_tx extends uvm_sequence_item;
  `uvm_object_utils(base_tx)

  int value;

  function new(string name = "base_tx");
    super.new(name);
    value = 100;  // Base class sets value to 100
  endfunction

  virtual function string get_type_info();
    return "base_tx";
  endfunction

  virtual function void print_info();
    $display("base_tx: value=%0d, type_info=%s", value, get_type_info());
  endfunction
endclass

// Extended transaction class - overrides base_tx
class extended_tx extends base_tx;
  `uvm_object_utils(extended_tx)

  int extra_value;

  function new(string name = "extended_tx");
    super.new(name);
    value = 200;       // Extended class sets value to 200
    extra_value = 999;
  endfunction

  virtual function string get_type_info();
    return "extended_tx";
  endfunction

  virtual function void print_info();
    $display("extended_tx: value=%0d, extra_value=%0d, type_info=%s",
             value, extra_value, get_type_info());
  endfunction
endclass

module top;
  initial begin
    base_tx tx1, tx2, tx3;
    uvm_factory factory;
    uvm_object obj;

    $display("=== Factory Override Test ===");
    $display("");

    // Test 1: Create without override - should get base_tx
    $display("Test 1: Create base_tx without override (using $ivl_factory_create)");
    obj = $ivl_factory_create("base_tx");
    if (obj != null && $cast(tx1, obj)) begin
      tx1.print_info();
      if (tx1.value == 100 && tx1.get_type_info() == "base_tx")
        $display("  PASSED - Created base_tx as expected");
      else
        $display("  FAILED - Wrong type or value");
    end else begin
      $display("  FAILED - Could not create or cast base_tx");
    end
    $display("");

    // Test 2: Register type override
    $display("Test 2: Registering type override: base_tx -> extended_tx");
    factory = uvm_factory::get();
    factory.set_type_override_by_name("base_tx", "extended_tx");
    $display("  Override registered");
    $display("");

    // Test 3: Create after override - should get extended_tx
    $display("Test 3: Create 'base_tx' after override (should get extended_tx)");
    obj = $ivl_factory_create("base_tx");
    if (obj != null && $cast(tx2, obj)) begin
      tx2.print_info();
      if (tx2.value == 200 && tx2.get_type_info() == "extended_tx")
        $display("  PASSED - Factory created extended_tx via override!");
      else if (tx2.value == 100 && tx2.get_type_info() == "base_tx")
        $display("  PARTIAL - Factory created base_tx (override may not be working)");
      else
        $display("  FAILED - Unexpected type or value");
    end else begin
      $display("  FAILED - Could not create or cast");
    end
    $display("");

    // Test 4: Direct instantiation should still create base_tx
    $display("Test 4: Direct instantiation (should still be base_tx)");
    tx3 = new("tx3");
    tx3.print_info();
    if (tx3.value == 100 && tx3.get_type_info() == "base_tx")
      $display("  PASSED - Direct instantiation creates base_tx");
    else
      $display("  FAILED - Direct instantiation gave wrong type");
    $display("");

    // Final result
    $display("=== Test Complete ===");
    if (tx2 != null && tx2.value == 200)
      $display("PASSED - Factory type override is working!");
    else
      $display("PARTIAL - Factory type override needs more work");

    $finish;
  end
endmodule
