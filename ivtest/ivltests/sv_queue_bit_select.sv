// Test bit-select on queue elements
// This tests the pattern: queue[i][bit]

module test;

   class Container;
      bit [7:0] data[$];  // Queue of 8-bit values
   endclass

   initial begin
      Container c;
      int pass = 1;

      c = new();
      c.data.push_back(8'hA5);  // 10100101
      c.data.push_back(8'h5A);  // 01011010
      c.data.push_back(8'hF0);  // 11110000

      // Test bit-select on queue elements
      if (c.data[0][0] !== 1'b1) begin
         $display("FAIL: data[0][0] = %b, expected 1", c.data[0][0]);
         pass = 0;
      end
      if (c.data[0][7] !== 1'b1) begin
         $display("FAIL: data[0][7] = %b, expected 1", c.data[0][7]);
         pass = 0;
      end
      if (c.data[1][0] !== 1'b0) begin
         $display("FAIL: data[1][0] = %b, expected 0", c.data[1][0]);
         pass = 0;
      end
      if (c.data[1][7] !== 1'b0) begin
         $display("FAIL: data[1][7] = %b, expected 0", c.data[1][7]);
         pass = 0;
      end
      if (c.data[2][4] !== 1'b1) begin
         $display("FAIL: data[2][4] = %b, expected 1", c.data[2][4]);
         pass = 0;
      end

      // Test with variable index
      for (int i = 0; i < 3; i++) begin
         if (c.data[i][0] !== (i == 0 ? 1'b1 : (i == 1 ? 1'b0 : 1'b0))) begin
            $display("FAIL: data[%0d][0] mismatch", i);
            pass = 0;
         end
      end

      if (pass)
         $display("PASSED");
      else
         $display("FAILED");
   end

endmodule
