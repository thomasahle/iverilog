// Test named property declarations
// property foo; @(posedge clk) expr; endproperty
// assert property(foo);
module sv_named_property;
   logic clk = 0;
   logic rst = 1;
   logic a = 0;
   logic b = 0;

   always #5 clk = ~clk;

   // Track assertion results
   int pass_count = 0, fail_count = 0;

   // Named property with clocking event
   property p_a_implies_b;
      @(posedge clk) disable iff (!rst)
      a |-> b;
   endproperty

   // Named property without clocking event
   property p_simple;
      a || !b;
   endproperty

   // Use named property in assertion
   assert property(p_a_implies_b)
      pass_count++;
      else fail_count++;

   // Use named property with explicit clocking (overrides property's)
   assert property(@(posedge clk) p_simple)
      else fail_count++;

   always @(posedge clk) begin
      static int cycle = 0;
      cycle++;

      case (cycle)
         1: rst <= 1;
         2: begin a <= 1; b <= 1; end  // a=1, b=1 -> passes
         3: begin a <= 1; b <= 0; end  // a=1, b=0 -> fails (would fail p_a_implies_b)
         4: begin a <= 0; b <= 0; end  // a=0, don't care about b
         5: begin a <= 0; b <= 1; end  // a=0, don't care about b

         10: begin
            $display("Pass: %0d, Fail: %0d", pass_count, fail_count);
            // With the logic we set up, we expect some passes
            if (pass_count > 0)
               $display("PASSED");
            else
               $display("FAILED");
            $finish;
         end
      endcase
   end

endmodule
