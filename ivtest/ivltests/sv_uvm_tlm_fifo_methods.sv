// Test for UVM TLM FIFO is_full/is_empty methods
`include "uvm_macros.svh"

package test_pkg;
  import uvm_pkg::*;

  class simple_obj extends uvm_object;
    int value;
    `uvm_object_utils(simple_obj)
    function new(string name = "simple_obj");
      super.new(name);
    endfunction
  endclass

  class test_class extends uvm_test;
    `uvm_component_utils(test_class)

    uvm_tlm_analysis_fifo #(simple_obj) analysis_fifo;
    simple_obj obj;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      analysis_fifo = new("analysis_fifo", this);
    endfunction

    task run_phase(uvm_phase phase);
      phase.raise_objection(this);

      // Test is_empty on empty FIFO
      if (!analysis_fifo.is_empty()) begin
        `uvm_error("TEST", "analysis_fifo should be empty initially")
      end

      // Test is_full on empty FIFO
      if (analysis_fifo.is_full()) begin
        `uvm_error("TEST", "analysis_fifo should not be full initially")
      end

      // Add an item
      obj = new("obj");
      obj.value = 42;
      analysis_fifo.write(obj);

      // Test is_empty after adding item
      if (analysis_fifo.is_empty()) begin
        `uvm_error("TEST", "analysis_fifo should not be empty after write")
      end

      // Test size
      if (analysis_fifo.size() != 1) begin
        `uvm_error("TEST", $sformatf("analysis_fifo size should be 1, got %0d", analysis_fifo.size()))
      end

      `uvm_info("TEST", "PASSED", UVM_LOW)
      phase.drop_objection(this);
    endtask
  endclass
endpackage

module test;
  import uvm_pkg::*;
  import test_pkg::*;

  initial begin
    run_test("test_class");
  end
endmodule
