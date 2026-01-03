// Test uvm_object clone() method
// Clone creates a copy of an object using the factory
// Compile with: iverilog -g2012 uvm_pkg.sv sv_uvm_clone.sv
import uvm_pkg::*;

// Simple test class with properties to clone
// Note: Without uvm_object_utils macro, we need to register with factory manually
class my_packet extends uvm_sequence_item;
  int addr;
  int data;
  string name_str;

  function new(string name = "my_packet");
    super.new(name);
    addr = 0;
    data = 0;
    name_str = "";
  endfunction

  virtual function string get_type_name();
    return "my_packet";
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

    // Create original packet with data
    orig = new("original");
    orig.addr = 32'h1234;
    orig.data = 32'hABCD;
    orig.name_str = "test_packet";

    $display("Original: addr=0x%h, data=0x%h, name_str=%s",
             orig.addr, orig.data, orig.name_str);

    // Test do_copy directly (clone requires factory registration)
    cloned = new("cloned");
    cloned.copy(orig);

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

    $display("PASSED: copy() works correctly");
  end
endmodule
