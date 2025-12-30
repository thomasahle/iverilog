// Test interface arrays with always_comb routing (like APB testbench)

interface simple_if(input logic clk);
  logic [7:0] data;
  logic [1:0] sel;
  logic valid;
  logic ready;
endinterface

module master_bfm(simple_if intf);
  initial begin
    intf.data = 8'h00;
    intf.sel = 2'b00;
    intf.valid = 0;
    #20;
    intf.sel = 2'b01;  // Select slave 0
    intf.data = 8'hAB;
    intf.valid = 1;
    $display("[%0t] Master: sel=%b, data=0x%h, valid=%b", $time, intf.sel, intf.data, intf.valid);
    #20;
    intf.data = 8'hCD;
    $display("[%0t] Master: sel=%b, data=0x%h", $time, intf.sel, intf.data);
    #20;
    intf.valid = 0;
  end
endmodule

module slave_bfm #(parameter SLAVE_ID = 0) (simple_if intf);
  initial begin
    intf.ready = 0;
    #25;
    $display("[%0t] Slave[%0d]: data=0x%h, sel=%b, valid=%b", $time, SLAVE_ID, intf.data, intf.sel, intf.valid);
    intf.ready = 1;
    #20;
    $display("[%0t] Slave[%0d]: data=0x%h, sel=%b, valid=%b", $time, SLAVE_ID, intf.data, intf.sel, intf.valid);
  end
endmodule

module test;
  parameter NO_OF_SLAVES = 2;

  logic clk;

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Master interface
  simple_if intf(clk);

  // Slave interfaces array
  simple_if intf_s[NO_OF_SLAVES](clk);

  // Master BFM
  master_bfm master(.intf(intf));

  // Route signals from master to selected slave
  always_comb begin
    // Default: deselect all slaves
    intf_s[0].sel = 2'b00;
    intf_s[0].data = 8'h00;
    intf_s[0].valid = 0;
    intf_s[1].sel = 2'b00;
    intf_s[1].data = 8'h00;
    intf_s[1].valid = 0;

    case(intf.sel)
      2'b01: begin
        intf_s[0].sel = intf.sel;
        intf_s[0].data = intf.data;
        intf_s[0].valid = intf.valid;
        intf.ready = intf_s[0].ready;
      end
      2'b10: begin
        intf_s[1].sel = intf.sel;
        intf_s[1].data = intf.data;
        intf_s[1].valid = intf.valid;
        intf.ready = intf_s[1].ready;
      end
      default: begin
        intf.ready = 0;
      end
    endcase
  end

  // Slave BFMs
  genvar i;
  generate
    for (i = 0; i < NO_OF_SLAVES; i++) begin : slave_gen
      slave_bfm #(.SLAVE_ID(i)) slave(.intf(intf_s[i]));
    end
  endgenerate

  // Check
  initial begin
    #30;
    // Slave 0 should see the data
    if (intf_s[0].data !== 8'hAB) begin
      $display("FAILED: Slave 0 expected data=0xAB, got 0x%h", intf_s[0].data);
      $finish;
    end
    if (intf_s[0].valid !== 1) begin
      $display("FAILED: Slave 0 expected valid=1, got %b", intf_s[0].valid);
      $finish;
    end

    #50;
    $display("PASSED");
    $finish;
  end
endmodule
