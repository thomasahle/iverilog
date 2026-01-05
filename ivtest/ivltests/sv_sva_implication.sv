// Test SVA implication operators |-> and |=> in assertion context
module sv_sva_implication;
   logic clk = 0;
   logic req = 0;
   logic ack = 0;
   int pass_count = 0;

   always #5 clk = ~clk;

   // Counters for assertion pass/fail
   int ov_pass = 0, ov_fail = 0;
   int nov_pass = 0, nov_fail = 0;

   // Test |-> overlapping implication: req |-> ack
   assert property (@(posedge clk) req |-> ack) ov_pass++;
      else ov_fail++;

   // Test |=> non-overlapping implication: req |=> ack
   assert property (@(posedge clk) req |=> ack) nov_pass++;
      else nov_fail++;

   always @(posedge clk) begin
      static int cycle = 0;
      cycle++;

      case (cycle)
         1: begin
            req <= 0; ack <= 0;  // Vacuously true for |->
         end
         2: begin
            req <= 0; ack <= 0;  // Vacuously true for |->
         end
         3: begin
            req <= 1; ack <= 0;  // |-> should fail
         end
         4: begin
            req <= 1; ack <= 1;  // |-> should pass
         end
         5: begin
            req <= 1; ack <= 0;  // |=> setup (req true now)
         end
         6: begin
            req <= 0; ack <= 1;  // |=> should pass (was req, now ack)
         end
         7: begin
            req <= 1; ack <= 0;  // |=> setup again
         end
         8: begin
            req <= 0; ack <= 0;  // |=> should fail (was req, no ack)
         end

         10: begin
            $display("Overlapping |->: PASS=%0d, FAIL=%0d", ov_pass, ov_fail);
            $display("Non-overlapping |=>: PASS=%0d, FAIL=%0d", nov_pass, nov_fail);
            // We expect some passes and some fails
            if (ov_pass > 0 && ov_fail > 0 && nov_pass > 0 && nov_fail > 0)
               $display("PASSED");
            else
               $display("FAILED");
            $finish;
         end
      endcase
   end

endmodule
