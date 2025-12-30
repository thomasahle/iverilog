// Test with NO_OF_SLAVES=2 (2-bit pselx) - should work

parameter int NO_OF_SLAVES = 2;  // 2 bits
parameter int DATA_WIDTH = 32;

interface data_if(input logic clk);
  logic [NO_OF_SLAVES-1:0] pselx;  // 2-bit signal
  logic [DATA_WIDTH-1:0] data;
  logic penable;
  logic pready;
endinterface

// Slave driver interface
interface slave_driver_bfm #(parameter SLAVE_ID = 0) (
  input bit clk,
  input bit psel,
  input logic penable,
  output bit pready
);
  initial begin
    pready = 0;
    $display("[%0t] slave_driver_bfm[%0d]: Initialized", $time, SLAVE_ID);
  end

  task wait_for_setup();
    @(posedge clk);
    $display("[%0t] slave_driver_bfm[%0d]: Waiting for psel", $time, SLAVE_ID);
    while (psel !== 1) begin
      @(negedge clk);
    end
    $display("[%0t] slave_driver_bfm[%0d]: Got psel=1!", $time, SLAVE_ID);
    @(posedge clk);
    pready = 1;
    $display("[%0t] slave_driver_bfm[%0d]: Asserting pready", $time, SLAVE_ID);
  endtask
endinterface

// Slave agent
module slave_agent_bfm #(parameter int SLAVE_ID = 0) (data_if intf);
  slave_driver_bfm #(.SLAVE_ID(SLAVE_ID)) slave_drv(
    .clk(intf.clk),
    .psel(intf.pselx[SLAVE_ID]),  // Bit select for this slave
    .penable(intf.penable),
    .pready(intf.pready)
  );

  initial begin
    slave_drv.wait_for_setup();
  end
endmodule

// Master driver interface
interface master_driver_bfm(
  input bit clk,
  output logic [NO_OF_SLAVES-1:0] pselx,
  output logic penable,
  input bit pready
);
  initial begin
    pselx = 0;
    penable = 0;
    #30;
    pselx = 2'b01;  // Select slave 0
    $display("[%0t] master_driver_bfm: Driving pselx=%b", $time, pselx);
    @(posedge clk);
    penable = 1;
    $display("[%0t] master_driver_bfm: Driving penable=1", $time);
    wait(pready == 1);
    $display("[%0t] master_driver_bfm: Got pready!", $time);
    @(posedge clk);
    pselx = 0;
    penable = 0;
  end
endinterface

// Master agent
module master_agent_bfm(data_if intf);
  master_driver_bfm master_drv(
    .clk(intf.clk),
    .pselx(intf.pselx),
    .penable(intf.penable),
    .pready(intf.pready)
  );
endmodule

module test;
  logic clk;

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Master interface
  data_if intf(clk);

  // Slave interface array
  data_if intf_s[NO_OF_SLAVES](clk);

  // Master agent
  master_agent_bfm master(.intf(intf));

  // Route from master to slaves
  always_comb begin
    // Default
    intf_s[0].pselx = 'b0;
    intf_s[0].penable = 'b0;
    intf_s[1].pselx = 'b0;
    intf_s[1].penable = 'b0;
    intf.pready = 'b0;

    case(intf.pselx)
      2'b01: begin
        intf_s[0].pselx = intf.pselx;
        intf_s[0].penable = intf.penable;
        intf.pready = intf_s[0].pready;
      end
      2'b10: begin
        intf_s[1].pselx = intf.pselx;
        intf_s[1].penable = intf.penable;
        intf.pready = intf_s[1].pready;
      end
    endcase
  end

  // Slave agents in generate block
  genvar i;
  generate
    for (i = 0; i < NO_OF_SLAVES; i++) begin : slave_gen
      slave_agent_bfm #(.SLAVE_ID(i)) slave(.intf(intf_s[i]));
    end
  endgenerate

  // Timeout
  initial begin
    #500;
    $display("FAILED: Timeout");
    $finish;
  end

  // Success check
  initial begin
    wait(intf.pready == 1);
    #20;
    $display("PASSED");
    $finish;
  end
endmodule
