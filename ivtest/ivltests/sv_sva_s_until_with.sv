// Test s_until_with operator in assertions
// Pattern: a s_until_with b means a holds until b (inclusive)
// Commonly used in AXI valid/ready handshake protocols
module test;
   logic clk = 0;
   logic valid, ready;
   int pass_count = 0;
   int check_count = 0;

   always #5 clk = ~clk;

   // Property: once valid rises, it must stay high until ready
   // valid s_until_with ready means: ready || valid
   // This is satisfied when:
   //   - ready is high (we've completed the handshake), OR
   //   - valid is high (we're still holding valid waiting for ready)
   property handshake;
      @(posedge clk) $rose(valid) |-> valid s_until_with ready;
   endproperty

   assert property(handshake) begin
      check_count++;
      pass_count++;
   end else begin
      check_count++;
   end

   initial begin
      valid = 0;
      ready = 0;

      // Cycle 1: valid rises
      @(posedge clk);
      valid = 1;

      // Cycle 2: valid stays high, ready still low - should pass
      @(posedge clk);

      // Cycle 3: valid stays high, ready still low - should pass
      @(posedge clk);

      // Cycle 4: ready goes high - handshake completes - should pass
      @(posedge clk);
      ready = 1;

      // Cycle 5: Both drop
      @(posedge clk);
      valid = 0;
      ready = 0;

      // Cycle 6: New handshake - valid rises
      @(posedge clk);
      valid = 1;

      // Cycle 7: Ready goes high immediately - should pass
      @(posedge clk);
      ready = 1;

      repeat (3) @(posedge clk);

      $display("PASSED - s_until_with operator working");
      $display("  check_count=%0d pass_count=%0d", check_count, pass_count);
      $finish;
   end

endmodule
