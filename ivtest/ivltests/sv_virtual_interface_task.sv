// Test calling tasks through virtual interface from config_db
// Mimics the exact AXI4 AVIP pattern with main_if and BFM interfaces

import uvm_pkg::*;

// Main interface with bus signals (like axi4_if)
interface main_if(input bit clk, input bit rst_n);
  logic [7:0] data;
  logic valid;
  logic ready;
endinterface

// Driver BFM interface that connects to main interface (like axi4_master_driver_bfm)
interface driver_bfm(input bit clk, input bit rst_n,
                     output logic [7:0] data,
                     output logic valid,
                     input logic ready);
  string name = "driver_bfm";

  // Wait for reset task (like wait_for_aresetn)
  task wait_for_reset();
    $display("@ %0t: %s: wait_for_reset: waiting for negedge", $time, name);
    @(negedge rst_n);
    $display("@ %0t: %s: wait_for_reset: got negedge", $time, name);
    @(posedge rst_n);
    $display("@ %0t: %s: wait_for_reset: got posedge, done", $time, name);
  endtask

  // Drive data task (like axi4_write_address_channel_task)
  task drive_data(input logic [7:0] d);
    $display("@ %0t: %s: drive_data: starting with d=%h", $time, name, d);
    @(posedge clk);
    valid <= 1'b1;
    data <= d;
    $display("@ %0t: %s: drive_data: asserted valid", $time, name);
    // Wait for ready (like waiting for awready)
    while (!ready) begin
      @(posedge clk);
    end
    @(posedge clk);
    valid <= 1'b0;
    $display("@ %0t: %s: drive_data: done", $time, name);
  endtask
endinterface

// Agent BFM module that wraps driver BFM (like axi4_master_agent_bfm)
module agent_bfm(main_if intf);
  // Instantiate driver BFM with connections to main interface
  driver_bfm drv_bfm(.clk(intf.clk),
                     .rst_n(intf.rst_n),
                     .data(intf.data),
                     .valid(intf.valid),
                     .ready(intf.ready));

  initial begin
    $display("@ %0t: agent_bfm: setting drv_bfm in config_db", $time);
    uvm_config_db#(virtual driver_bfm)::set(null, "*", "driver_bfm", drv_bfm);
  end
endmodule

// UVM-like driver proxy class
class driver_proxy extends uvm_component;
  virtual driver_bfm vbfm;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual driver_bfm)::get(this, "", "driver_bfm", vbfm)) begin
      $display("FAILED: Could not get driver_bfm from config_db");
    end else begin
      $display("@ %0t: driver_proxy: got driver_bfm from config_db", $time);
    end
  endfunction

  task run_phase(uvm_phase phase);
    $display("@ %0t: driver_proxy: run_phase starting", $time);
    vbfm.wait_for_reset();
    $display("@ %0t: driver_proxy: wait_for_reset returned, calling drive_data", $time);
    vbfm.drive_data(8'hAB);
    $display("@ %0t: driver_proxy: drive_data returned", $time);
  endtask
endclass

// Simple test
class my_test extends uvm_test;
  driver_proxy drv;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    drv = new("drv", this);
    drv.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    $display("@ %0t: my_test: run_phase starting", $time);

    fork
      drv.run_phase(phase);
    join_none

    #200;

    phase.drop_objection(this);
  endtask

  function void report_phase(uvm_phase phase);
    if ($time > 0)
      $display("PASSED");
    else
      $display("FAILED - time stuck at 0");
  endfunction
endclass

module test;
  bit clk = 0;
  bit rst_n = 1;

  // Clock generation
  always #5 clk = ~clk;

  // Reset generation
  initial begin
    rst_n = 1;
    #20 rst_n = 0;
    #20 rst_n = 1;
  end

  // Main interface instance
  main_if intf(.clk(clk), .rst_n(rst_n));

  // Agent BFM instance with interface port (like AXI4 pattern)
  agent_bfm agent(.intf(intf));

  // Run test
  initial begin
    run_test("my_test");
  end
endmodule
