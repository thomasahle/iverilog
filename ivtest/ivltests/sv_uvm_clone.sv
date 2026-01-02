// Test uvm_object clone() method
// Clone creates a copy of an object using the factory

`include "uvm_macros.svh"
`include "uvm_pkg.sv"
import uvm_pkg::*;

// Simple test class with properties to clone
class my_packet extends uvm_sequence_item;
  int addr;
  int data;
  string name_str;

  `uvm_object_utils(my_packet)

  function new(string name = "my_packet");
    super.new(name);
    addr = 0;
    data = 0;
    name_str = "";
  endfunction

  // Copy fields from rhs
  virtual function void do_copy(uvm_object rhs);
    my_packet pkt;
    super.do_copy(rhs);
    if ($cast(pkt, rhs)) begin
      this.addr = pkt.addr;
      this.data = pkt.data;
      this.name_str = pkt.name_str;
    end
  endfunction
endclass

module test;
  initial begin
    my_packet orig;
    my_packet cloned;
    uvm_object obj;

    // Create original packet with data
    orig = new("original");
    orig.addr = 32'h1234;
    orig.data = 32'hABCD;
    orig.name_str = "test_packet";

    $display("Original: addr=0x%h, data=0x%h, name_str=%s",
             orig.addr, orig.data, orig.name_str);

    // Clone it
    obj = orig.clone();

    if (obj == null) begin
      $display("FAIL: clone() returned null");
      $finish;
    end

    // Cast to packet type
    if (!$cast(cloned, obj)) begin
      $display("FAIL: Could not cast cloned object to my_packet");
      $finish;
    end

    $display("Cloned: addr=0x%h, data=0x%h, name_str=%s",
             cloned.addr, cloned.data, cloned.name_str);

    // Verify values were copied
    if (cloned.addr !== orig.addr) begin
      $display("FAIL: addr not copied correctly");
      $finish;
    end

    if (cloned.data !== orig.data) begin
      $display("FAIL: data not copied correctly");
      $finish;
    end

    if (cloned.name_str != orig.name_str) begin
      $display("FAIL: name_str not copied correctly");
      $finish;
    end

    // Verify it's a different object (modify cloned, orig unchanged)
    cloned.addr = 32'h9999;
    if (orig.addr === cloned.addr) begin
      $display("FAIL: Clone is not independent (same object?)");
      $finish;
    end

    $display("PASSED: clone() works correctly");
  end
endmodule
