// Test case statement with width mismatch (like APB with NO_OF_SLAVES=1)
// When pselx is 1-bit and case uses 2-bit literals

interface data_if(input logic clk);
  logic [0:0] sel;  // 1-bit signal (NO_OF_SLAVES=1)
  logic [7:0] data;
  logic valid;
  logic ready;
endinterface

module test;
  logic clk;

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Master and slave interfaces
  data_if intf_master(clk);
  data_if intf_slave[1](clk);

  // Route signals using case with width mismatch
  always_comb begin
    case(intf_master.sel)  // 1-bit signal
      2'b01: begin         // 2-bit literal
        intf_slave[0].sel = intf_master.sel[0];  // bit-select on 1-bit
        intf_slave[0].data = intf_master.data;
        intf_slave[0].valid = intf_master.valid;
        intf_master.ready = intf_slave[0].ready;
      end
      default: begin
        intf_slave[0].sel = 'b0;
        intf_slave[0].valid = 'b0;
        intf_master.ready = 'b0;
      end
    endcase
  end

  // Drive master
  initial begin
    intf_master.sel = 0;
    intf_master.data = 8'h00;
    intf_master.valid = 0;

    #20;
    $display("[%0t] Before drive: master.sel=%b, slave[0].sel=%b",
             $time, intf_master.sel, intf_slave[0].sel);

    intf_master.sel = 1'b1;  // 1-bit value
    intf_master.data = 8'hAB;
    intf_master.valid = 1;
    $display("[%0t] After drive: master.sel=%b (width=%0d bits)",
             $time, intf_master.sel, $bits(intf_master.sel));

    #1;  // Allow combinational logic to settle
    $display("[%0t] After settle: slave[0].sel=%b, slave[0].data=0x%h, slave[0].valid=%b",
             $time, intf_slave[0].sel, intf_slave[0].data, intf_slave[0].valid);
  end

  // Check routing
  initial begin
    #25;
    // master.sel = 1 (1-bit), should match case 2'b01
    if (intf_slave[0].sel !== 1'b1) begin
      $display("FAILED: Expected slave[0].sel=1, got %b", intf_slave[0].sel);
      $display("  master.sel = %b (binary), %0d (decimal)", intf_master.sel, intf_master.sel);
      $display("  Case 2'b01 = %0d (decimal)", 2'b01);
      $finish;
    end
    if (intf_slave[0].data !== 8'hAB) begin
      $display("FAILED: Expected slave[0].data=0xAB, got 0x%h", intf_slave[0].data);
      $finish;
    end
    if (intf_slave[0].valid !== 1'b1) begin
      $display("FAILED: Expected slave[0].valid=1, got %b", intf_slave[0].valid);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
