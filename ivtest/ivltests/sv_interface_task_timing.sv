// Test interface BFM pattern like AXI4 AVIP
// Tests the reset wait and driver task pattern

import uvm_pkg::*;

interface driver_bfm(input bit clk, input bit rst_n);
  logic [7:0] data;
  logic valid;
  logic ready;

  string name = "driver_bfm";

  // Wait for reset sequence - like AXI4 pattern
  task wait_for_reset();
    $display("@ %0t: %s: wait_for_reset: waiting for negedge rst_n", $time, name);
    @(negedge rst_n);
    $display("@ %0t: %s: wait_for_reset: got negedge, waiting for posedge", $time, name);
    @(posedge rst_n);
    $display("@ %0t: %s: wait_for_reset: reset complete", $time, name);
  endtask

  // Drive data task - like AXI4 channel task
  task drive_data(input logic [7:0] d);
    $display("@ %0t: %s: drive_data: starting with d=%h", $time, name, d);
    @(posedge clk);
    valid <= 1'b1;
    data <= d;
    $display("@ %0t: %s: drive_data: asserted valid", $time, name);

    // Wait for ready (like AXI handshake)
    while (!ready) begin
      @(posedge clk);
      $display("@ %0t: %s: drive_data: waiting for ready", $time, name);
    end

    @(posedge clk);
    valid <= 1'b0;
    $display("@ %0t: %s: drive_data: done", $time, name);
  endtask
endinterface

interface responder_bfm(input bit clk, input bit rst_n);
  logic ready;

  string name = "responder_bfm";

  // Wait for reset
  task wait_for_reset();
    $display("@ %0t: %s: wait_for_reset: waiting", $time, name);
    @(negedge rst_n);
    @(posedge rst_n);
    $display("@ %0t: %s: wait_for_reset: done", $time, name);
  endtask

  // Respond with ready after delay
  task respond_ready(input int delay_cycles);
    $display("@ %0t: %s: respond_ready: waiting %0d cycles", $time, name, delay_cycles);
    repeat(delay_cycles) @(posedge clk);
    ready <= 1'b1;
    $display("@ %0t: %s: respond_ready: asserted ready", $time, name);
    @(posedge clk);
    ready <= 1'b0;
  endtask
endinterface

// UVM-like driver proxy class
class driver_proxy extends uvm_component;
  virtual driver_bfm vbfm;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    $display("@ %0t: driver_proxy: run_phase starting", $time);
    vbfm.wait_for_reset();
    $display("@ %0t: driver_proxy: calling drive_data", $time);
    vbfm.drive_data(8'hAB);
    $display("@ %0t: driver_proxy: run_phase done", $time);
  endtask
endclass

// UVM-like responder proxy class
class responder_proxy extends uvm_component;
  virtual responder_bfm vbfm;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    $display("@ %0t: responder_proxy: run_phase starting", $time);
    vbfm.wait_for_reset();
    $display("@ %0t: responder_proxy: responding with ready", $time);
    vbfm.respond_ready(3);
    $display("@ %0t: responder_proxy: run_phase done", $time);
  endtask
endclass

module test;
  bit clk = 0;
  bit rst_n = 1;

  // Clock generation
  always #5 clk = ~clk;

  // Reset generation - like APB/AXI4 pattern
  initial begin
    rst_n = 1;
    #12 rst_n = 0;
    #20 rst_n = 1;
  end

  // BFM instances
  driver_bfm drv_bfm(.clk(clk), .rst_n(rst_n));
  responder_bfm rsp_bfm(.clk(clk), .rst_n(rst_n));

  // Connect ready signal
  assign drv_bfm.ready = rsp_bfm.ready;

  // Test
  initial begin
    driver_proxy drv;
    responder_proxy rsp;

    $display("@ %0t: test: starting", $time);

    drv = new("drv", null);
    rsp = new("rsp", null);

    // Set BFM handles (like config_db::set/get)
    drv.vbfm = drv_bfm;
    rsp.vbfm = rsp_bfm;

    // Run both proxies in parallel (like UVM run_phase)
    fork
      drv.run_phase(null);
      rsp.run_phase(null);
    join

    $display("@ %0t: test: done", $time);

    if ($time > 0) begin
      $display("PASSED");
    end else begin
      $display("FAILED - time stuck at 0");
    end

    $finish;
  end
endmodule
