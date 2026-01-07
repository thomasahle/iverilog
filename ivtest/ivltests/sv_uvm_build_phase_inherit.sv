// Test UVM-style build_phase inheritance pattern
// This tests the exact pattern that was broken: a derived test class
// that doesn't override build_phase should still execute the base
// test class's build_phase which creates child components.

`include "uvm_pkg.sv"


module test;
  import uvm_pkg::*;

  int errors = 0;

  // Simple component that tracks if it was created
  class my_component extends uvm_component;
    `uvm_component_utils(my_component)

    static int instances_created = 0;
    int instance_id;

    function new(string name = "my_component", uvm_component parent = null);
      super.new(name, parent);
      instances_created++;
      instance_id = instances_created;
      $display("my_component::new() - instance %0d created: %s", instance_id, name);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      $display("my_component::build_phase() for instance %0d", instance_id);
    endfunction
  endclass

  // Base test class that creates a component in build_phase
  class base_test extends uvm_test;
    `uvm_component_utils(base_test)

    my_component comp;  // This should be created in build_phase

    function new(string name = "base_test", uvm_component parent = null);
      super.new(name, parent);
      $display("base_test::new()");
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      $display("base_test::build_phase() - creating component");
      comp = my_component::type_id::create("comp", this);
    endfunction

    task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      $display("base_test::run_phase() - checking if comp was created");
      if (comp == null) begin
        $display("FAILED: comp is null - build_phase didn't run!");
        errors++;
      end else begin
        $display("PASSED: comp was created (instance %0d)", comp.instance_id);
      end
      phase.drop_objection(this);
    endtask
  endclass

  // Derived test that does NOT override build_phase
  // It should inherit and execute base_test::build_phase
  class derived_test extends base_test;
    `uvm_component_utils(derived_test)

    function new(string name = "derived_test", uvm_component parent = null);
      super.new(name, parent);
      $display("derived_test::new()");
    endfunction

    // NOTE: NO build_phase override - should use base_test::build_phase

    task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      $display("derived_test::run_phase() - checking if comp was created");
      if (comp == null) begin
        $display("FAILED: comp is null in derived_test - inherited build_phase didn't run!");
        errors++;
      end else begin
        $display("PASSED: comp was created by inherited build_phase (instance %0d)", comp.instance_id);
      end
      phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
      if (errors == 0)
        $display("PASSED");
      else
        $display("FAILED: %0d errors", errors);
    endfunction
  endclass

  initial begin
    $display("=== Testing UVM build_phase inheritance ===");
    $display("This tests that derived_test inherits and executes base_test::build_phase");
    $display("");
    run_test("derived_test");
  end
endmodule
