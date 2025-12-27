// Test: config_db storing and retrieving virtual interface handles
// Pattern used by UVM components to pass interfaces

interface simple_if(input logic clk);
  logic data;
  logic valid;
endinterface

class config_obj;
  virtual simple_if vif;
  int value;

  function new();
    value = 42;
  endfunction
endclass

class agent_config;
  virtual simple_if drv_vif;
  int agent_id;
endclass

module test;
  logic clk = 0;
  simple_if sif(clk);

  // Simple storage - using module-level variables instead of static class members
  config_obj cfg_store;
  agent_config agent_store;

  initial begin
    automatic config_obj cfg_set, cfg_get;
    automatic agent_config agent_set, agent_get;
    automatic int errors = 0;

    // Test 1: Store config with virtual interface
    cfg_set = new();
    cfg_set.vif = sif;
    cfg_set.value = 100;
    cfg_store = cfg_set;

    // Test 2: Retrieve config and check virtual interface
    cfg_get = cfg_store;
    if (cfg_get == null) begin
      $display("FAILED: cfg_get is null");
      errors++;
    end else begin
      if (cfg_get.value != 100) begin
        $display("FAILED: Wrong value %0d, expected 100", cfg_get.value);
        errors++;
      end
      if (cfg_get.vif == null) begin
        $display("FAILED: Retrieved vif is null");
        errors++;
      end else begin
        $display("Config vif retrieved successfully");
      end
    end

    // Test 3: Store agent config with virtual interface
    agent_set = new();
    agent_set.drv_vif = sif;
    agent_set.agent_id = 5;
    agent_store = agent_set;

    // Test 4: Retrieve agent config
    agent_get = agent_store;
    if (agent_get == null) begin
      $display("FAILED: agent_get is null");
      errors++;
    end else begin
      if (agent_get.agent_id != 5) begin
        $display("FAILED: Wrong agent_id %0d, expected 5", agent_get.agent_id);
        errors++;
      end
      if (agent_get.drv_vif == null) begin
        $display("FAILED: Retrieved drv_vif is null");
        errors++;
      end else begin
        $display("Agent drv_vif retrieved successfully");
      end
    end

    // Test 5: Access interface through retrieved config
    if (cfg_get.vif != null) begin
      cfg_get.vif.data = 1;
      cfg_get.vif.valid = 1;
      #1;
      if (sif.data !== 1 || sif.valid !== 1) begin
        $display("FAILED: Interface signals not set correctly");
        errors++;
      end else begin
        $display("Interface access through config works");
      end
    end

    // Test 6: Nested access - config contains vif, access vif signals
    if (agent_get.drv_vif != null) begin
      agent_get.drv_vif.data = 0;
      agent_get.drv_vif.valid = 0;
      #1;
      if (sif.data !== 0 || sif.valid !== 0) begin
        $display("FAILED: Agent interface signals not set correctly");
        errors++;
      end else begin
        $display("Agent interface access through config works");
      end
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
