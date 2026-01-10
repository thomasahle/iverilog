// Test virtual interface with modport specification in class properties
// IEEE 1800-2017: 25.9 Virtual interfaces

interface simple_if(input logic clk);
  logic data;
  logic valid;

  modport driver(output data, output valid);
  modport monitor(input data, input valid);
endinterface

class Driver;
  // Virtual interface with modport specification
  virtual simple_if.driver vif;

  function new(virtual simple_if.driver v);
    vif = v;
  endfunction

  task drive(bit d, bit v);
    vif.data = d;
    vif.valid = v;
  endtask
endclass

class Monitor;
  // Virtual interface with modport specification
  virtual simple_if.monitor vif;

  function new(virtual simple_if.monitor v);
    vif = v;
  endfunction

  function void check(bit expected_data, bit expected_valid);
    if (vif.data !== expected_data || vif.valid !== expected_valid) begin
      $display("FAILED: data=%b (expected %b), valid=%b (expected %b)",
               vif.data, expected_data, vif.valid, expected_valid);
      $finish;
    end
  endfunction
endclass

module test;
  logic clk = 0;
  simple_if intf(clk);

  initial begin
    automatic Driver drv;
    automatic Monitor mon;

    drv = new(intf);
    mon = new(intf);

    // Test drive and monitor
    drv.drive(1, 1);
    #1;
    mon.check(1, 1);

    drv.drive(0, 1);
    #1;
    mon.check(0, 1);

    drv.drive(1, 0);
    #1;
    mon.check(1, 0);

    $display("PASSED");
  end
endmodule
