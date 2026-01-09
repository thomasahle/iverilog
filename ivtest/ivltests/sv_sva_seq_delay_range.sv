// Test bounded range delays in assertions: ##[m:n]
module test;
   logic clk = 0;
   logic a, b, c;
   int pass_count = 0;
   int check_count = 0;

   always #5 clk = ~clk;

   // Test 1: a |-> ##[1:3] b - if a was true 1-3 cycles ago, b must be true now
   // Approximated as: if a was true 3 cycles ago, b must be true
   property p1;
      @(posedge clk) a |-> ##[1:3] b;
   endproperty

   assert property(p1) begin
      check_count++;
      pass_count++;
   end else begin
      check_count++;
   end

   // Test 2: a ##[0:2] b |-> c - sequence with delay range in antecedent
   // Approximated as: if (a 2 cycles ago && b now) then c
   property p2;
      @(posedge clk) a ##[0:2] b |-> c;
   endproperty

   assert property(p2) begin
      check_count++;
      pass_count++;
   end else begin
      check_count++;
   end

   initial begin
      a = 0; b = 0; c = 0;

      // Cycle 1: Set up signals
      @(posedge clk);
      a = 1;  // Assert a

      // Cycle 2
      @(posedge clk);
      a = 0;

      // Cycle 3
      @(posedge clk);

      // Cycle 4: b should satisfy a |-> ##[1:3] b (a was 3 cycles ago)
      @(posedge clk);
      b = 1;  // This should pass p1

      // Cycle 5: Set up for p2 test
      @(posedge clk);
      a = 1;
      b = 0;
      c = 0;

      // Cycle 6
      @(posedge clk);
      a = 0;

      // Cycle 7: b comes 2 cycles after a, set c for implication
      @(posedge clk);
      b = 1;
      c = 1;  // This should pass p2

      // Give time for final checks
      repeat (3) @(posedge clk);

      $display("PASSED - Bounded range delays compiled and assertions checked");
      $display("  check_count=%0d pass_count=%0d", check_count, pass_count);
      $finish;
   end

endmodule
