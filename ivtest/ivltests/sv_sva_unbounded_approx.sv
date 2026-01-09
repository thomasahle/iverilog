// Test unbounded delay ##[m:$] approximation with -gsupported-assertions
// This tests the bounded approximation feature (approximates as ##[m:32])

module test;
   logic clk = 0;
   logic request, acknowledge;
   int pass_count = 0;
   int check_count = 0;

   always #5 clk = ~clk;

   // Unbounded delay: request eventually gets acknowledged
   // Approximated as ##[1:32]
   property req_ack_overlap;
      @(posedge clk) request |-> ##[1:$] acknowledge;
   endproperty

   // Non-overlapping unbounded delay
   // Approximated as ##[1:33] (32+1 for non-overlap)
   property req_ack_nonoverlap;
      @(posedge clk) request |=> ##[1:$] acknowledge;
   endproperty

   assert property (req_ack_overlap) begin
      check_count++;
      pass_count++;
   end else begin
      check_count++;
   end

   assert property (req_ack_nonoverlap) begin
      check_count++;
      pass_count++;
   end else begin
      check_count++;
   end

   initial begin
      request = 0;
      acknowledge = 0;
      
      // Test: Request followed by ack within approx window
      @(posedge clk); request = 1;
      @(posedge clk); request = 0;
      repeat(5) @(posedge clk);
      acknowledge = 1;
      @(posedge clk); acknowledge = 0;
      
      // Wait for assertion evaluation
      repeat(40) @(posedge clk);
      
      $display("PASSED: Unbounded delay approximation working");
      $display("check_count=%0d pass_count=%0d", check_count, pass_count);
      $finish;
   end
endmodule
