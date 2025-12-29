// Test uvm_config_db suffix matching with virtual interfaces
// Tests that "env" matches "uvm_test_top.env" etc.
// Uses virtual interface (object) config_db which properly extracts component context

`include "uvm_macros.svh"
`include "uvm_pkg.sv"

interface simple_if;
  logic [7:0] data;
  logic valid;
endinterface

module test;
  import uvm_pkg::*;

  simple_if sif();
  int errors = 0;

  // Deep component hierarchy for testing suffix matching
  class driver_comp extends uvm_component;
    `uvm_component_utils(driver_comp)
    virtual simple_if vif;

    function new(string name = "driver_comp", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // Get "driver_vif" - should match suffix "driver" in our full path
      if (!uvm_config_db#(virtual simple_if)::get(this, "", "driver_vif", vif)) begin
        $display("FAILED: driver could not get driver_vif");
        errors++;
      end else if (vif == null) begin
        $display("FAILED: driver vif is null");
        errors++;
      end else begin
        $display("PASSED: driver got driver_vif");
      end
    endfunction
  endclass

  class agent_comp extends uvm_component;
    `uvm_component_utils(agent_comp)
    driver_comp driver;
    virtual simple_if vif;

    function new(string name = "agent_comp", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // Get "agent_vif" - should match suffix "agent" in our full path
      if (!uvm_config_db#(virtual simple_if)::get(this, "", "agent_vif", vif)) begin
        $display("FAILED: agent could not get agent_vif");
        errors++;
      end else if (vif == null) begin
        $display("FAILED: agent vif is null");
        errors++;
      end else begin
        $display("PASSED: agent got agent_vif");
      end

      // Pass vif to driver before creating
      uvm_config_db#(virtual simple_if)::set(null, "driver", "driver_vif", vif);

      // Create driver
      driver = driver_comp::type_id::create("driver", this);
    endfunction
  endclass

  class env_comp extends uvm_component;
    `uvm_component_utils(env_comp)
    agent_comp agent;
    virtual simple_if vif;

    function new(string name = "env_comp", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // Get "env_vif" - should match suffix "env" in "uvm_test_top.env"
      if (!uvm_config_db#(virtual simple_if)::get(this, "", "env_vif", vif)) begin
        $display("FAILED: env could not get env_vif");
        errors++;
      end else if (vif == null) begin
        $display("FAILED: env vif is null");
        errors++;
      end else begin
        $display("PASSED: env got env_vif");
      end

      // Pass vif to agent before creating
      uvm_config_db#(virtual simple_if)::set(null, "agent", "agent_vif", vif);

      // Create agent
      agent = agent_comp::type_id::create("agent", this);
    endfunction
  endclass

  class test_comp extends uvm_test;
    `uvm_component_utils(test_comp)
    env_comp env;
    virtual simple_if vif;

    function new(string name = "test_comp", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // Get "test_vif" - should match exact path "uvm_test_top"
      if (!uvm_config_db#(virtual simple_if)::get(this, "", "test_vif", vif)) begin
        $display("FAILED: test could not get test_vif");
        errors++;
      end else if (vif == null) begin
        $display("FAILED: test vif is null");
        errors++;
      end else begin
        $display("PASSED: test got test_vif");
      end

      // Pass vif to env before creating
      uvm_config_db#(virtual simple_if)::set(null, "env", "env_vif", vif);

      // Create env
      env = env_comp::type_id::create("env", this);
    endfunction

    task run_phase(uvm_phase phase);
      phase.raise_objection(this);

      // Test that all components got the same interface
      if (vif != null) begin
        vif.data = 8'hCD;
        #1;
      end

      if (env.vif != null && env.vif.data == 8'hCD) begin
        $display("PASSED: env sees same interface");
      end else begin
        $display("FAILED: env interface mismatch");
        errors++;
      end

      if (env.agent.vif != null && env.agent.vif.data == 8'hCD) begin
        $display("PASSED: agent sees same interface");
      end else begin
        $display("FAILED: agent interface mismatch");
        errors++;
      end

      if (env.agent.driver.vif != null && env.agent.driver.vif.data == 8'hCD) begin
        $display("PASSED: driver sees same interface");
      end else begin
        $display("FAILED: driver interface mismatch");
        errors++;
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
    // Set vif for test at top level with exact path
    uvm_config_db#(virtual simple_if)::set(null, "uvm_test_top", "test_vif", sif);

    // Run the test
    run_test("test_comp");
  end
endmodule
