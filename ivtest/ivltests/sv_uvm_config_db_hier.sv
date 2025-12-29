// Test uvm_config_db hierarchical path matching
// This tests the suffix matching feature where "env" matches "uvm_test_top.env"
// This is the key pattern used for passing virtual interfaces to child components

`include "uvm_macros.svh"
`include "uvm_pkg.sv"

interface simple_if;
  logic [7:0] data;
  logic valid;
endinterface

module test;
  import uvm_pkg::*;

  simple_if sif();

  // Child component that gets vif from config_db
  class my_driver extends uvm_component;
    `uvm_component_utils(my_driver)

    virtual simple_if vif;

    function new(string name = "my_driver", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // Get uses "this" as context with empty inst_name
      // This should match what parent set with "driver" inst_name
      if (!uvm_config_db#(virtual simple_if)::get(this, "", "vif", vif)) begin
        `uvm_fatal("NOVIF", $sformatf("Virtual interface not found for %s", get_full_name()))
      end
      `uvm_info("DRIVER", $sformatf("Got virtual interface in %s", get_full_name()), UVM_LOW)
    endfunction
  endclass

  // Agent containing driver
  class my_agent extends uvm_component;
    `uvm_component_utils(my_agent)

    my_driver drv;
    virtual simple_if vif;

    function new(string name = "my_agent", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      // Get vif from parent using hierarchical matching
      // Parent set with inst_name = "agent", we get with this context = "uvm_test_top.env.agent"
      if (!uvm_config_db#(virtual simple_if)::get(this, "", "vif", vif)) begin
        `uvm_fatal("NOVIF", $sformatf("Virtual interface not found for %s", get_full_name()))
      end
      `uvm_info("AGENT", $sformatf("Got virtual interface in %s", get_full_name()), UVM_LOW)

      // Pass vif to child driver
      uvm_config_db#(virtual simple_if)::set(null, "driver", "vif", vif);

      // Create driver
      drv = my_driver::type_id::create("driver", this);
    endfunction
  endclass

  // Environment containing agent
  class my_env extends uvm_component;
    `uvm_component_utils(my_env)

    my_agent agent;
    virtual simple_if vif;

    function new(string name = "my_env", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      // Get vif from parent - parent set with inst_name = "env"
      // We get with this context = "uvm_test_top.env"
      if (!uvm_config_db#(virtual simple_if)::get(this, "", "vif", vif)) begin
        `uvm_fatal("NOVIF", $sformatf("Virtual interface not found for %s", get_full_name()))
      end
      `uvm_info("ENV", $sformatf("Got virtual interface in %s", get_full_name()), UVM_LOW)

      // Pass vif to agent
      uvm_config_db#(virtual simple_if)::set(null, "agent", "vif", vif);

      // Create agent
      agent = my_agent::type_id::create("agent", this);
    endfunction
  endclass

  // Test class
  class my_test extends uvm_test;
    `uvm_component_utils(my_test)

    my_env env;
    virtual simple_if vif;

    function new(string name = "my_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      // Get vif from top-level - set with inst_name = "uvm_test_top"
      // We get with this context = "uvm_test_top"
      if (!uvm_config_db#(virtual simple_if)::get(this, "", "vif", vif)) begin
        `uvm_fatal("NOVIF", "Virtual interface not found in test")
      end
      `uvm_info("TEST", "Got virtual interface in test", UVM_LOW)

      // Pass vif to env
      uvm_config_db#(virtual simple_if)::set(null, "env", "vif", vif);

      // Create env
      env = my_env::type_id::create("env", this);
    endfunction

    task run_phase(uvm_phase phase);
      phase.raise_objection(this);

      // Test that we can access the interface through the hierarchy
      if (vif != null) begin
        vif.data = 8'hAB;
        vif.valid = 1;
        #10;
        `uvm_info("TEST", $sformatf("Set vif.data=0x%0h, vif.valid=%0b", vif.data, vif.valid), UVM_LOW)
      end

      // Verify env got the same interface
      if (env.vif != null && env.vif.data == 8'hAB) begin
        `uvm_info("TEST", "Env sees same interface data", UVM_LOW)
      end else begin
        `uvm_error("TEST", "Env interface mismatch")
      end

      // Verify agent got the same interface
      if (env.agent.vif != null && env.agent.vif.data == 8'hAB) begin
        `uvm_info("TEST", "Agent sees same interface data", UVM_LOW)
      end else begin
        `uvm_error("TEST", "Agent interface mismatch")
      end

      // Verify driver got the same interface
      if (env.agent.drv.vif != null && env.agent.drv.vif.data == 8'hAB) begin
        `uvm_info("TEST", "Driver sees same interface data", UVM_LOW)
      end else begin
        `uvm_error("TEST", "Driver interface mismatch")
      end

      phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
      // All passed if we got here without UVM_FATAL
      $display("PASSED");
    endfunction
  endclass

  initial begin
    // Set vif for test at top-level with null context
    uvm_config_db#(virtual simple_if)::set(null, "uvm_test_top", "vif", sif);

    // Run the test
    run_test("my_test");
  end
endmodule
