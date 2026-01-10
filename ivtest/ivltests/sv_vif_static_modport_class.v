// Test static virtual interface with modport specification in class properties
// IEEE 1800-2017: 25.9 Virtual interfaces

interface simple_if(input logic clk);
  logic data;
  logic valid;

  modport driver(output data, output valid);
  modport monitor(input data, input valid);
endinterface

class Driver;
  // Static virtual interface with modport specification
  static virtual simple_if.driver vif;

  static function void set_interface(virtual simple_if.driver v);
    vif = v;
  endfunction

  static task drive(bit d, bit v);
    vif.data = d;
    vif.valid = v;
  endtask
endclass

class Monitor;
  // Static virtual interface with modport specification
  static virtual simple_if.monitor vif;

  static function void set_interface(virtual simple_if.monitor v);
    vif = v;
  endfunction

  static function void check(bit expected_data, bit expected_valid);
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
    Driver::set_interface(intf);
    Monitor::set_interface(intf);

    // Test drive and monitor
    Driver::drive(1, 1);
    #1;
    Monitor::check(1, 1);

    Driver::drive(0, 1);
    #1;
    Monitor::check(0, 1);

    Driver::drive(1, 0);
    #1;
    Monitor::check(1, 0);

    $display("PASSED");
  end
endmodule
