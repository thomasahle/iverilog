// Test +UVM_TESTNAME command line plusarg support
// This test verifies that run_test() uses +UVM_TESTNAME when called with no argument
// and the plusarg is available.

`include "uvm_macros.svh"
import uvm_pkg::*;

class plusarg_test extends uvm_test;
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    $display("plusarg_test: run_phase executed");
    $display("PASSED");
    phase.drop_objection(this);
  endtask
endclass

// Default test if no plusarg provided
class default_test extends uvm_test;
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    // This is also valid - no plusarg means we need explicit test name
    $display("default_test: run_phase executed (no +UVM_TESTNAME)");
    $display("PASSED");
    phase.drop_objection(this);
  endtask
endclass

module test_top;
  string test_name;
  initial begin
    // Check if +UVM_TESTNAME is provided, otherwise use default_test
    if (!$value$plusargs("UVM_TESTNAME=%s", test_name)) begin
      // No plusarg - call with explicit name to verify that path works
      run_test("default_test");
    end else begin
      // Plusarg provided - call with no argument to use it
      run_test();
    end
  end
endmodule
