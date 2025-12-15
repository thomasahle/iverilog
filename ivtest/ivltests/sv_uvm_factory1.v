// Test UVM factory pattern
// Tests type_id::create and run_test

`include "uvm_macros.svh"
`include "uvm_pkg.sv"

import uvm_pkg::*;

class my_transaction extends uvm_sequence_item;
  `uvm_object_utils(my_transaction)

  int data;
  int addr;

  function new(string name = "my_transaction");
    super.new(name);
    data = 0;
    addr = 0;
  endfunction

  function void set_values(int d, int a);
    data = d;
    addr = a;
  endfunction
endclass

class my_component extends uvm_component;
  `uvm_component_utils(my_component)

  int count;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    count = 0;
  endfunction

  function void increment();
    count++;
  endfunction
endclass

module test;
  my_transaction txn;
  my_component comp;

  initial begin
    // Test object creation via type_id::create
    txn = my_transaction::type_id::create("txn1");
    if (txn == null) begin
      $display("FAILED: type_id::create returned null for transaction");
      $finish;
    end

    // Test object functionality
    txn.set_values(100, 200);
    if (txn.data != 100 || txn.addr != 200) begin
      $display("FAILED: transaction values not set correctly");
      $finish;
    end

    // Test component creation via type_id::create
    comp = my_component::type_id::create("comp1", null);
    if (comp == null) begin
      $display("FAILED: type_id::create returned null for component");
      $finish;
    end

    // Test component functionality
    comp.increment();
    comp.increment();
    if (comp.count != 2) begin
      $display("FAILED: component count = %0d, expected 2", comp.count);
      $finish;
    end

    $display("PASSED");
  end
endmodule
