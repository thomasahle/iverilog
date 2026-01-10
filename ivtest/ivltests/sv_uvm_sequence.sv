// Test UVM sequence base functionality
// Compile with: iverilog -g2012 -I<uvm_dir> sv_uvm_sequence.sv

`include "uvm_pkg.sv"
`include "uvm_macros.svh"

package test_pkg;
  import uvm_pkg::*;

  class my_item extends uvm_sequence_item;
    `uvm_object_utils(my_item)

    rand int data;
    rand logic [7:0] addr;

    function new(string name = "my_item");
      super.new(name);
    endfunction
  endclass

  class my_sequence extends uvm_sequence #(my_item);
    `uvm_object_utils(my_sequence)

    function new(string name = "my_sequence");
      super.new(name);
    endfunction

    virtual task body();
      my_item item;
      item = my_item::type_id::create("item");
      if (item.randomize()) begin
        `uvm_info(get_type_name(), $sformatf("Generated item: data=%0d, addr=%0d", item.data, item.addr), UVM_LOW)
      end
    endtask
  endclass

endpackage

module test;
  import uvm_pkg::*;
  import test_pkg::*;

  initial begin
    my_sequence seq;
    my_item item;

    // Test sequence item creation
    item = my_item::type_id::create("test_item");
    if (item == null) begin
      $display("FAILED: Could not create my_item");
      $finish;
    end
    $display("Created item: %s", item.get_type_name());

    // Test randomize
    if (!item.randomize()) begin
      $display("FAILED: randomize() returned 0");
      $finish;
    end
    $display("Randomized item: data=%0d, addr=%0d", item.data, item.addr);

    // Test sequence creation
    seq = my_sequence::type_id::create("test_seq");
    if (seq == null) begin
      $display("FAILED: Could not create my_sequence");
      $finish;
    end
    $display("Created sequence: %s", seq.get_type_name());

    $display("PASSED");
    $finish;
  end
endmodule
