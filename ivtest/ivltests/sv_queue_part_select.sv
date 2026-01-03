// Test part-select on queue/darray elements
// Pattern: queue[i][base -: width] and queue[i][base +: width]
module test;

   class Container;
      bit [31:0] data[$];  // Queue of 32-bit values

      function void add(bit [31:0] val);
         data.push_back(val);
      endfunction
   endclass

   int pass = 1;

   initial begin
      Container c;
      bit [7:0] byte_val;

      c = new();
      c.add(32'hDEADBEEF);  // Element 0
      c.add(32'h12345678);  // Element 1

      // Test indexed down-select: [base -: width]
      // data[0] = 32'hDEADBEEF
      // data[0][7 -: 8] should get bits [7:0] = 8'hEF
      byte_val = c.data[0][7 -: 8];
      if (byte_val != 8'hEF) begin
         $display("FAILED: data[0][7 -: 8] = %h, expected EF", byte_val);
         pass = 0;
      end

      // data[0][15 -: 8] should get bits [15:8] = 8'hBE
      byte_val = c.data[0][15 -: 8];
      if (byte_val != 8'hBE) begin
         $display("FAILED: data[0][15 -: 8] = %h, expected BE", byte_val);
         pass = 0;
      end

      // data[0][23 -: 8] should get bits [23:16] = 8'hAD
      byte_val = c.data[0][23 -: 8];
      if (byte_val != 8'hAD) begin
         $display("FAILED: data[0][23 -: 8] = %h, expected AD", byte_val);
         pass = 0;
      end

      // data[0][31 -: 8] should get bits [31:24] = 8'hDE
      byte_val = c.data[0][31 -: 8];
      if (byte_val != 8'hDE) begin
         $display("FAILED: data[0][31 -: 8] = %h, expected DE", byte_val);
         pass = 0;
      end

      // Test indexed up-select: [base +: width]
      // data[1] = 32'h12345678
      // data[1][0 +: 8] should get bits [7:0] = 8'h78
      byte_val = c.data[1][0 +: 8];
      if (byte_val != 8'h78) begin
         $display("FAILED: data[1][0 +: 8] = %h, expected 78", byte_val);
         pass = 0;
      end

      // data[1][8 +: 8] should get bits [15:8] = 8'h56
      byte_val = c.data[1][8 +: 8];
      if (byte_val != 8'h56) begin
         $display("FAILED: data[1][8 +: 8] = %h, expected 56", byte_val);
         pass = 0;
      end

      // Test with variable index for array element
      for (int i = 0; i < 2; i++) begin
         byte_val = c.data[i][7 -: 8];
         if (i == 0 && byte_val != 8'hEF) begin
            $display("FAILED: data[%0d][7 -: 8] = %h, expected EF", i, byte_val);
            pass = 0;
         end
         if (i == 1 && byte_val != 8'h78) begin
            $display("FAILED: data[%0d][7 -: 8] = %h, expected 78", i, byte_val);
            pass = 0;
         end
      end

      if (pass)
         $display("PASSED");
   end

endmodule
