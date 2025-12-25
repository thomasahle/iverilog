// Test basic UVM class inheritance and macros
`include "uvm_macros.svh"
`include "uvm_pkg.sv"
import uvm_pkg::*;

class my_object extends uvm_object;
  `uvm_object_utils(my_object)

  int data;

  function new(string name = "my_object");
    super.new(name);
    data = 42;
  endfunction

  virtual function void do_print(uvm_printer printer);
    printer.print_field("data", data, 32, UVM_DEC);
  endfunction
endclass

class my_component extends uvm_component;
  `uvm_component_utils(my_component)

  my_object obj;

  function new(string name = "my_component", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    obj = new("my_obj");
    obj.data = 100;
  endfunction
endclass

module test;
  initial begin
    my_object obj;
    my_component comp;

    // Test object creation
    obj = new("test_obj");
    if (obj.data != 42) begin
      $display("FAILED: object data should be 42, got %0d", obj.data);
      $finish;
    end

    // Test component creation
    comp = new("test_comp", null);

    // Test build phase
    comp.build_phase(null);
    if (comp.obj.data != 100) begin
      $display("FAILED: component obj.data should be 100, got %0d", comp.obj.data);
      $finish;
    end

    // Test type names
    if (obj.get_type_name() != "my_object") begin
      $display("FAILED: object type name should be my_object");
      $finish;
    end

    if (comp.get_type_name() != "my_component") begin
      $display("FAILED: component type name should be my_component");
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
