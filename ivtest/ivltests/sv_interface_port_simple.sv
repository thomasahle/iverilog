// Test basic interface port connectivity between modules
// This tests if interface ports properly connect signals

interface simple_if(input logic clk);
  logic [7:0] data;
  logic valid;
  logic ready;
endinterface

module master_bfm(simple_if intf);
  initial begin
    intf.data = 8'h00;
    intf.valid = 0;
    #20;
    intf.data = 8'hAB;
    intf.valid = 1;
    $display("[%0t] Master: Driving data=0x%h, valid=%b", $time, intf.data, intf.valid);
    #20;
    intf.data = 8'hCD;
    $display("[%0t] Master: Driving data=0x%h, valid=%b", $time, intf.data, intf.valid);
    #20;
    intf.valid = 0;
    $display("[%0t] Master: valid=%b", $time, intf.valid);
  end
endmodule

module slave_bfm(simple_if intf);
  initial begin
    intf.ready = 0;
    #25;
    $display("[%0t] Slave: Seeing data=0x%h, valid=%b", $time, intf.data, intf.valid);
    intf.ready = 1;
    #20;
    $display("[%0t] Slave: Seeing data=0x%h, valid=%b", $time, intf.data, intf.valid);
    #20;
  end
endmodule

module test;
  logic clk;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Interface instantiation
  simple_if intf(clk);

  // Module instantiation with interface ports
  master_bfm master(.intf(intf));
  slave_bfm slave(.intf(intf));

  // Check connectivity
  initial begin
    #30;
    // At t=30, master has data=0xAB, valid=1
    if (intf.data !== 8'hAB) begin
      $display("FAILED: Expected data=0xAB at t=30, got 0x%h", intf.data);
      $finish;
    end
    if (intf.valid !== 1) begin
      $display("FAILED: Expected valid=1 at t=30, got %b", intf.valid);
      $finish;
    end

    #20;
    // At t=50, master has data=0xCD
    if (intf.data !== 8'hCD) begin
      $display("FAILED: Expected data=0xCD at t=50, got 0x%h", intf.data);
      $finish;
    end

    #30;
    $display("PASSED");
    $finish;
  end
endmodule
