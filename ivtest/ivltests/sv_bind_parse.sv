// Test bind directive parsing
// IEEE 1800-2017 Section 23.11
// Note: Bind is parsed but not yet fully elaborated

// Target module to bind into
module target_dut(
  input wire clk,
  input wire rst,
  input wire [7:0] data_in,
  output wire [7:0] data_out
);
  reg [7:0] data_reg;
  assign data_out = data_reg;

  always @(posedge clk or posedge rst) begin
    if (rst)
      data_reg <= 8'b0;
    else
      data_reg <= data_in;
  end
endmodule

// Checker module to be bound
module data_checker(
  input wire clk,
  input wire [7:0] data
);
  // Simple checker - would normally have assertions
  initial $display("data_checker instantiated");
endmodule

// Another checker
module reset_checker(
  input wire clk,
  input wire rst
);
  // Reset checker
  initial $display("reset_checker instantiated");
endmodule

module test;
  reg clk;
  reg rst;
  reg [7:0] data_in;
  wire [7:0] data_out;

  target_dut dut(
    .clk(clk),
    .rst(rst),
    .data_in(data_in),
    .data_out(data_out)
  );

  // Bind directives - parser should accept these
  // Bind checker to all instances of target_dut
  bind target_dut data_checker dc_inst(.clk(clk), .data(data_in));

  // Another bind with different checker
  bind target_dut reset_checker rc_inst(.clk(clk), .rst(rst));

  initial begin
    clk = 0;
    rst = 1;
    data_in = 8'h00;

    #10 rst = 0;
    #10 data_in = 8'hAB;
    #10 data_in = 8'hCD;
    #10;

    // If we get here, the bind was parsed successfully
    $display("PASSED - bind directive parsed successfully");
    $finish;
  end

  always #5 clk = ~clk;
endmodule
