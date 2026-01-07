// Test $sampled() system function
// $sampled(expr) returns the value of expr from the previous sample point
module sv_sva_sampled;
   logic clk = 0;
   logic [7:0] data = 0;
   int pass_count = 0;
   int sample_count = 0;
   logic [7:0] expected_sampled;
   logic [7:0] actual_sampled;

   always #5 clk = ~clk;

   // Check $sampled at each clock edge
   always @(posedge clk) begin
      sample_count++;
      actual_sampled = $sampled(data);  // Capture once to avoid multiple calls

      case (sample_count)
         1: expected_sampled = 8'h00;  // First sample, returns current
         2: expected_sampled = 8'h00;  // Previous was 00
         3: expected_sampled = 8'hAA;  // Previous was AA
         4: expected_sampled = 8'hBB;  // Previous was BB
         default: expected_sampled = 8'hCC;
      endcase

      if (actual_sampled == expected_sampled) begin
         $display("Sample %0d PASSED: data=%h, sampled=%h (expected %h)",
                  sample_count, data, actual_sampled, expected_sampled);
         pass_count++;
      end else begin
         $display("Sample %0d FAILED: data=%h, sampled=%h, expected=%h",
                  sample_count, data, actual_sampled, expected_sampled);
      end
   end

   initial begin
      #12 data = 8'hAA;  // Change before t=15 posedge
      #10 data = 8'hBB;  // Change before t=25 posedge
      #10 data = 8'hCC;  // Change before t=35 posedge
      #20;

      if (pass_count >= 4) begin
         $display("PASSED: $sampled() test completed successfully");
      end else begin
         $display("FAILED: Only %0d of 4+ tests passed", pass_count);
      end
      $finish;
   end
endmodule
