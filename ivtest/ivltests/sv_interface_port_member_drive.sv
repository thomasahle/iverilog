// Test: Interface port with child interface accessing individual members
// This mirrors the APB testbench pattern where:
// - Parent module receives interface as port
// - Parent module connects interface members to child interface
// - Child interface drives signals, which should update original interface

interface data_if(input logic clk);
  logic [7:0] data;
  logic valid;
  logic ready;
endinterface

// Child interface that drives individual signals (like apb_master_driver_bfm)
interface driver_bfm(input logic clk,
                     output logic [7:0] data,
                     output logic valid,
                     input logic ready);

  initial begin
    data = 8'h00;
    valid = 0;
    #20;
    data = 8'hAB;
    valid = 1;
    $display("[%0t] driver_bfm: Driving data=0x%h, valid=%b", $time, data, valid);
    #20;
    data = 8'hCD;
    $display("[%0t] driver_bfm: Driving data=0x%h", $time, data);
    #20;
    valid = 0;
  end
endinterface

// Parent module that takes interface port and connects to child (like apb_master_agent_bfm)
module agent_bfm(data_if intf);
  // Connect interface members to child interface ports
  driver_bfm drv(.clk(intf.clk),
                 .data(intf.data),
                 .valid(intf.valid),
                 .ready(intf.ready));

  initial begin
    $display("[%0t] agent_bfm: instantiated with interface port", $time);
  end
endmodule

// Observer module
module observer(data_if intf);
  initial begin
    #25;
    $display("[%0t] observer: Seeing data=0x%h, valid=%b", $time, intf.data, intf.valid);
    #20;
    $display("[%0t] observer: Seeing data=0x%h, valid=%b", $time, intf.data, intf.valid);
  end
endmodule

module test;
  logic clk;

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Interface instance
  data_if intf(clk);

  // Parent module with interface port
  agent_bfm agent(.intf(intf));

  // Observer module with interface port
  observer obs(.intf(intf));

  // Combinational logic reading interface (like hdl_top's always_comb)
  logic [7:0] routed_data;
  logic routed_valid;

  always_comb begin
    routed_data = intf.data;
    routed_valid = intf.valid;
  end

  // Check connectivity
  initial begin
    #30;
    // At t=30, driver should have driven data=0xAB, valid=1
    $display("[%0t] test: intf.data=0x%h, intf.valid=%b", $time, intf.data, intf.valid);
    $display("[%0t] test: routed_data=0x%h, routed_valid=%b", $time, routed_data, routed_valid);

    if (intf.data !== 8'hAB) begin
      $display("FAILED: Expected intf.data=0xAB at t=30, got 0x%h", intf.data);
      $finish;
    end
    if (intf.valid !== 1) begin
      $display("FAILED: Expected intf.valid=1 at t=30, got %b", intf.valid);
      $finish;
    end
    if (routed_data !== 8'hAB) begin
      $display("FAILED: Expected routed_data=0xAB, got 0x%h", routed_data);
      $finish;
    end

    #20;
    // At t=50, driver should have driven data=0xCD
    if (intf.data !== 8'hCD) begin
      $display("FAILED: Expected data=0xCD at t=50, got 0x%h", intf.data);
      $finish;
    end

    #30;
    $display("PASSED");
    $finish;
  end
endmodule
