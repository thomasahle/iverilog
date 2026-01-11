// Test basic virtual interface usage
// Verifies: virtual interface declaration, passing, signal access

interface simple_if(input logic clk);
  logic [7:0] data;
  logic valid;

  modport driver(output data, output valid);
  modport monitor(input data, input valid);
endinterface

class Driver;
  virtual simple_if vif;

  function new(virtual simple_if v);
    vif = v;
  endfunction

  task run();
    @(posedge vif.clk);
    vif.data <= 8'hAB;
    vif.valid <= 1;
    @(posedge vif.clk);
    vif.valid <= 0;
    @(posedge vif.clk);
    vif.data <= 8'hCD;
    vif.valid <= 1;
    @(posedge vif.clk);
    vif.valid <= 0;
    $display("Driver: Sent two packets");
  endtask
endclass

class Monitor;
  virtual simple_if vif;
  int count;

  function new(virtual simple_if v);
    vif = v;
    count = 0;
  endfunction

  task run();
    repeat (2) begin
      @(posedge vif.clk);
      while (!vif.valid) @(posedge vif.clk);
      $display("Monitor: Captured data 0x%h", vif.data);
      count++;
    end
  endtask
endclass

module test;
  logic clk;
  simple_if sif(clk);

  Driver drv;
  Monitor mon;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    // Initialize
    sif.data = 0;
    sif.valid = 0;

    // Create driver and monitor with virtual interfaces
    drv = new(sif);
    mon = new(sif);

    // Run in parallel
    fork
      drv.run();
      mon.run();
    join

    if (mon.count != 2) begin
      $display("FAILED: Monitor count = %0d, expected 2", mon.count);
      $finish;
    end

    $display("Virtual interface test completed");
    $display("PASSED");
    $finish;
  end
endmodule
