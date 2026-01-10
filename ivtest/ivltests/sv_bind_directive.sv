// Test bind directive parsing and storage
// The bind directive should bind an assertion module to a target module

module target_dut (
   input clk,
   input rst_n,
   input [7:0] data_in,
   output logic [7:0] data_out
);
   always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n)
         data_out <= 8'h00;
      else
         data_out <= data_in;
   end
endmodule

// Assertion module to be bound
module bound_assertions (
   input clk,
   input rst_n,
   input [7:0] data
);
   // Simple assertion checking data is not X after reset
   property data_valid_after_reset;
      @(posedge clk) rst_n |-> !$isunknown(data);
   endproperty

   assert property(data_valid_after_reset)
      else $error("Data contains X after reset");
endmodule

// File-scope bind directive
bind target_dut bound_assertions u_assert (
   .clk(clk),
   .rst_n(rst_n),
   .data(data_out)
);

module test;
   logic clk = 0;
   logic rst_n;
   logic [7:0] data_in;
   wire [7:0] data_out;

   target_dut dut (
      .clk(clk),
      .rst_n(rst_n),
      .data_in(data_in),
      .data_out(data_out)
   );

   always #5 clk = ~clk;

   initial begin
      rst_n = 0;
      data_in = 8'h00;
      #20;
      rst_n = 1;
      #10;
      data_in = 8'hAB;
      #10;
      data_in = 8'hCD;
      #10;
      $display("PASSED");
      $finish;
   end
endmodule
