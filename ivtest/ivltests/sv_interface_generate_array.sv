// Test interface arrays with generate block instances
// This replicates the APB testbench pattern where slaves are in a generate loop

interface data_if(input logic clk);
  logic [7:0] data;
  logic [1:0] sel;
  logic valid;
  logic ready;
endinterface

// Child interface that drives signals (like apb_slave_driver_bfm)
interface slave_bfm #(parameter SLAVE_ID = 0) (
  input logic clk,
  input logic [7:0] data,
  input logic sel,
  input logic valid,
  output logic ready
);
  initial begin
    ready = 0;
    $display("[%0t] slave_bfm[%0d]: Initialized", $time, SLAVE_ID);
  end

  always @(posedge clk) begin
    $display("[%0t] slave_bfm[%0d]: data=0x%h, sel=%b, valid=%b",
             $time, SLAVE_ID, data, sel, valid);
    if (sel && valid) begin
      #5 ready = 1;
      $display("[%0t] slave_bfm[%0d]: Asserting ready", $time, SLAVE_ID);
    end else begin
      ready = 0;
    end
  end
endinterface

// Parent module that connects interface to child (like apb_slave_agent_bfm)
module slave_agent_bfm #(parameter SLAVE_ID = 0) (data_if intf);
  slave_bfm #(.SLAVE_ID(SLAVE_ID)) slave(
    .clk(intf.clk),
    .data(intf.data),
    .sel(intf.sel[0]),
    .valid(intf.valid),
    .ready(intf.ready)
  );
endmodule

// Master interface
interface master_bfm(
  input logic clk,
  output logic [7:0] data,
  output logic [1:0] sel,
  output logic valid,
  input logic ready
);
  initial begin
    data = 8'h00;
    sel = 2'b00;
    valid = 0;
    #30;
    sel = 2'b01;  // Select slave 0
    data = 8'hAB;
    valid = 1;
    $display("[%0t] master_bfm: Driving sel=%b, data=0x%h, valid=%b", $time, sel, data, valid);

    // Wait for ready
    wait(ready == 1);
    $display("[%0t] master_bfm: Got ready!", $time);
    #10;
    valid = 0;
  end
endinterface

// Master agent
module master_agent_bfm(data_if intf);
  master_bfm master(
    .clk(intf.clk),
    .data(intf.data),
    .sel(intf.sel),
    .valid(intf.valid),
    .ready(intf.ready)
  );
endmodule

module test;
  parameter NO_OF_SLAVES = 2;

  logic clk;

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Master interface
  data_if intf(clk);

  // Slave interfaces array
  data_if intf_s[NO_OF_SLAVES](clk);

  // Master agent
  master_agent_bfm master(.intf(intf));

  // Route signals from master to selected slave
  always_comb begin
    // Default: deselect all slaves
    intf_s[0].sel = 2'b00;
    intf_s[0].data = 8'h00;
    intf_s[0].valid = 0;
    intf_s[1].sel = 2'b00;
    intf_s[1].data = 8'h00;
    intf_s[1].valid = 0;
    intf.ready = 0;

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
    endcase
  end

  // Slave agents in generate block (like APB testbench)
  genvar i;
  generate
    for (i = 0; i < NO_OF_SLAVES; i++) begin : slave_gen
      slave_agent_bfm #(.SLAVE_ID(i)) slave(.intf(intf_s[i]));
    end
  endgenerate

  // Timeout
  initial begin
    #200;
    $display("FAILED: Timeout - ready never asserted");
    $finish;
  end

  // Check
  initial begin
    wait(intf.ready == 1);
    $display("[%0t] test: ready asserted!", $time);
    #20;
    $display("PASSED");
    $finish;
  end
endmodule
