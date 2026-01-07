// Test config_db with enum types stored to class properties
// This tests the fix where config_db::set stores vec4 values
// and config_db::get retrieves them into class properties

`include "uvm_pkg.sv"

import uvm_pkg::*;

typedef enum bit [1:0] {
  MODE_A = 2'b00,
  MODE_B = 2'b01,
  MODE_C = 2'b10
} test_mode_e;

// Simulates an agent config class with enum property
class agent_config extends uvm_component;
  `uvm_component_utils(agent_config)
  test_mode_e read_data_mode;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    read_data_mode = MODE_A;
  endfunction
endclass

// Simulates a test that sets enum configs
class my_test extends uvm_test;
  `uvm_component_utils(my_test)
  agent_config agent_cfg_h;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent_cfg_h = agent_config::type_id::create("agent_cfg_h", this);

    // Set enum value in config_db (similar to AXI4 base_test)
    uvm_config_db#(test_mode_e)::set(this, "*", "read_data_mode", MODE_C);
    `uvm_info(get_type_name(), "Set read_data_mode = MODE_C", UVM_LOW)
  endfunction

  function void connect_phase(uvm_phase phase);
    // Get enum value from config_db (similar to AXI4 agent)
    if (uvm_config_db#(test_mode_e)::get(this, "", "read_data_mode", agent_cfg_h.read_data_mode)) begin
      `uvm_info(get_type_name(), $sformatf("Got read_data_mode = %s", agent_cfg_h.read_data_mode.name()), UVM_LOW)
      if (agent_cfg_h.read_data_mode == MODE_C) begin
        `uvm_info(get_type_name(), "PASSED: Enum config_db get works", UVM_LOW)
      end else begin
        `uvm_error(get_type_name(), $sformatf("FAILED: Expected MODE_C, got %s", agent_cfg_h.read_data_mode.name()))
      end
    end else begin
      `uvm_error(get_type_name(), "FAILED: config_db::get returned 0")
    end
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    #10;
    phase.drop_objection(this);
  endtask

  function void report_phase(uvm_phase phase);
    if (agent_cfg_h.read_data_mode == MODE_C)
      $display("PASSED");
    else
      $display("FAILED");
  endfunction
endclass

module test;
  initial run_test("my_test");
endmodule
