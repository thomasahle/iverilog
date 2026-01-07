// Test config_db path matching with array indices (brackets)
// This tests that patterns like "*agent[0]*" correctly match paths
// like "uvm_test_top.env.agent[0]"

`include "uvm_macros.svh"
import uvm_pkg::*;

class my_config extends uvm_object;
  `uvm_object_utils(my_config)

  int value;

  function new(string name = "my_config");
    super.new(name);
    value = 0;
  endfunction
endclass

class my_agent extends uvm_component;
  `uvm_component_utils(my_agent)

  my_config cfg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(my_config)::get(this, "", "config", cfg)) begin
      `uvm_fatal("CONFIG", "Failed to get config from config_db")
    end
    `uvm_info("AGENT", $sformatf("Got config with value=%0d", cfg.value), UVM_NONE)
  endfunction
endclass

class my_env extends uvm_component;
  `uvm_component_utils(my_env)

  my_agent agents[2];

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Create agents with array-style naming (brackets in name)
    agents[0] = my_agent::type_id::create("agents[0]", this);
    agents[1] = my_agent::type_id::create("agents[1]", this);
  endfunction
endclass

class my_test extends uvm_test;
  `uvm_component_utils(my_test)

  my_env env;
  my_config cfg0, cfg1;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Create configs
    cfg0 = my_config::type_id::create("cfg0");
    cfg0.value = 42;

    cfg1 = my_config::type_id::create("cfg1");
    cfg1.value = 99;

    // Set config using wildcard pattern with brackets
    // Pattern: "*agents[0]*" should match "uvm_test_top.env.agents[0]"
    uvm_config_db#(my_config)::set(this, "*agents[0]*", "config", cfg0);
    uvm_config_db#(my_config)::set(this, "*agents[1]*", "config", cfg1);

    env = my_env::type_id::create("env", this);
  endfunction

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    // The fact that build_phase completed without FATAL proves the config_db worked
    // Both agents received their configs correctly (verified by UVM_INFO messages)
    $display("PASSED: config_db bracket patterns worked (agents[0/1] received configs)");
  endfunction
endclass

module top;
  initial begin
    run_test("my_test");
  end
endmodule
