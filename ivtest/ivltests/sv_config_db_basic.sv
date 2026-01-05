// Test basic uvm_config_db functionality
// Tests set/get of objects via config_db

`include "uvm_macros.svh"
import uvm_pkg::*;

class my_config extends uvm_object;
  int value;
  string name_str;

  function new(string name = "my_config");
    super.new(name);
    value = 0;
    name_str = name;
  endfunction

  function void set_value(int v);
    value = v;
  endfunction
endclass

class my_component extends uvm_component;
  `uvm_component_utils(my_component)

  my_config cfg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Try to get config from config_db
    if (!uvm_config_db#(my_config)::get(this, "", "my_cfg", cfg)) begin
      $display("Config not found - creating default");
      cfg = new("default_cfg");
    end
  endfunction

  function void report();
    $display("Component %s has config value: %0d", get_name(), cfg.value);
  endfunction
endclass

class my_test extends uvm_test;
  `uvm_component_utils(my_test)

  my_component comp;
  my_config test_cfg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Create config and set in config_db
    test_cfg = new("test_cfg");
    test_cfg.set_value(42);
    uvm_config_db#(my_config)::set(this, "*", "my_cfg", test_cfg);

    // Create component
    comp = my_component::type_id::create("comp", this);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    comp.report();
    if (comp.cfg != null && comp.cfg.value == 42) begin
      $display("PASSED");
    end else begin
      $display("FAILED: config value mismatch");
    end
    phase.drop_objection(this);
  endtask
endclass

module test;
  initial begin
    run_test("my_test");
  end
endmodule
