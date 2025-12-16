// Test for UVM do_copy and do_compare methods
// Tests that the UVM sequence_item base class properly supports
// these methods for derived transaction classes

// Include UVM package directly for Icarus
`include "uvm_pkg.sv"

import uvm_pkg::*;

// A simple transaction class that overrides do_copy and do_compare
class my_transaction extends uvm_sequence_item;
  rand bit [7:0] data;
  rand bit [3:0] addr;
  bit valid;

  function new(string name = "my_transaction");
    super.new(name);
    data = 0;
    addr = 0;
    valid = 0;
  endfunction

  virtual function string get_type_name();
    return "my_transaction";
  endfunction

  // Override do_copy to copy fields from rhs
  virtual function void do_copy(uvm_object rhs);
    my_transaction rhs_tx;
    super.do_copy(rhs);
    // Cast rhs to our type
    if ($cast(rhs_tx, rhs)) begin
      data = rhs_tx.data;
      addr = rhs_tx.addr;
      valid = rhs_tx.valid;
    end
  endfunction

  // Override do_compare to compare fields
  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer = null);
    my_transaction rhs_tx;
    bit result;
    result = super.do_compare(rhs, comparer);
    if ($cast(rhs_tx, rhs)) begin
      result = result && (data == rhs_tx.data);
      result = result && (addr == rhs_tx.addr);
      result = result && (valid == rhs_tx.valid);
    end else begin
      result = 0;
    end
    return result;
  endfunction

  // Helper to set values
  function void set_values(bit [7:0] d, bit [3:0] a, bit v);
    data = d;
    addr = a;
    valid = v;
  endfunction
endclass

module test;
  initial begin
    my_transaction tx1, tx2, tx3;

    // Create transactions
    tx1 = new("tx1");
    tx2 = new("tx2");
    tx3 = new("tx3");

    // Set values in tx1
    tx1.set_values(8'hAB, 4'h5, 1);

    // Copy tx1 to tx2
    tx2.do_copy(tx1);

    // Check copy worked
    if (tx2.data != 8'hAB) begin
      $display("FAILED: tx2.data = %0h, expected AB", tx2.data);
      $finish;
    end
    if (tx2.addr != 4'h5) begin
      $display("FAILED: tx2.addr = %0h, expected 5", tx2.addr);
      $finish;
    end
    if (tx2.valid != 1) begin
      $display("FAILED: tx2.valid = %0b, expected 1", tx2.valid);
      $finish;
    end

    // Compare tx1 and tx2 - should match
    if (!tx1.do_compare(tx2)) begin
      $display("FAILED: tx1 and tx2 should compare equal");
      $finish;
    end

    // Compare tx1 and tx3 - should not match (tx3 has default values)
    if (tx1.do_compare(tx3)) begin
      $display("FAILED: tx1 and tx3 should not compare equal");
      $finish;
    end

    // Modify tx2 and compare again
    tx2.data = 8'hFF;
    if (tx1.do_compare(tx2)) begin
      $display("FAILED: tx1 and tx2 should not compare equal after modification");
      $finish;
    end

    $display("PASSED");
  end
endmodule
