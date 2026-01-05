// Test parameterized property declarations
// property foo(logic x, logic y); expr; endproperty
// assert property(foo(a, b));
module sv_param_property;
   logic clk = 0;
   logic rst = 1;
   logic a = 0;
   logic b = 0;
   logic c = 1;
   logic d = 1;

   always #5 clk = ~clk;

   // Track assertion results
   int pass_count = 0, fail_count = 0;

   // Parameterized property - checks that x implies y
   property p_implies(logic x, logic y);
      @(posedge clk) disable iff (!rst)
      x |-> y;
   endproperty

   // Use parameterized property with different arguments
   assert property(p_implies(a, b))
      pass_count++;
      else fail_count++;

   assert property(p_implies(c, d))
      pass_count++;
      else fail_count++;

   always @(posedge clk) begin
      static int cycle = 0;
      cycle++;

      case (cycle)
         1: rst <= 1;
         2: begin a <= 0; b <= 0; c <= 1; d <= 1; end  // a=0 (don't care), c->d passes
         3: begin a <= 1; b <= 1; c <= 1; d <= 1; end  // a->b passes, c->d passes
         4: begin a <= 1; b <= 0; c <= 1; d <= 0; end  // a->b fails, c->d fails
         5: begin a <= 0; b <= 1; c <= 0; d <= 1; end  // a=0, c=0 (don't care)

         10: begin
            $display("Pass: %0d, Fail: %0d", pass_count, fail_count);
            // We expect some passes and some fails
            if (pass_count > 0)
               $display("PASSED");
            else
               $display("FAILED");
            $finish;
         end
      endcase
   end

endmodule
