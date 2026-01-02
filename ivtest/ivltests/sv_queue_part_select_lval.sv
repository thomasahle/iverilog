// Test lvalue part-select on dynamic array/queue class property elements
// Tests patterns like: c.data[i][base -: width] = value

class Container;
   int data[$];  // Queue of 32-bit integers

   function void add(int val);
      data.push_back(val);
   endfunction
endclass

module test;
   initial begin
      Container c;
      int pass = 1;

      c = new();
      c.add(32'h00000000);  // data[0] = 0
      c.add(32'h00000000);  // data[1] = 0

      // Test 1: Simple lvalue part-select with constant base (down-select)
      c.data[0][7 -: 8] = 8'hEF;
      if (c.data[0] !== 32'h000000EF) begin
         $display("FAILED: Test 1 - c.data[0] = %h, expected 000000EF", c.data[0]);
         pass = 0;
      end

      // Test 2: Part-select on different byte
      c.data[0][15 -: 8] = 8'hBE;
      if (c.data[0] !== 32'h0000BEEF) begin
         $display("FAILED: Test 2 - c.data[0] = %h, expected 0000BEEF", c.data[0]);
         pass = 0;
      end

      // Test 3: Part-select on upper bytes
      c.data[0][23 -: 8] = 8'hAD;
      c.data[0][31 -: 8] = 8'hDE;
      if (c.data[0] !== 32'hDEADBEEF) begin
         $display("FAILED: Test 3 - c.data[0] = %h, expected DEADBEEF", c.data[0]);
         pass = 0;
      end

      // Test 4: Part-select on second element
      c.data[1][7 -: 8] = 8'h78;
      c.data[1][15 -: 8] = 8'h56;
      c.data[1][23 -: 8] = 8'h34;
      c.data[1][31 -: 8] = 8'h12;
      if (c.data[1] !== 32'h12345678) begin
         $display("FAILED: Test 4 - c.data[1] = %h, expected 12345678", c.data[1]);
         pass = 0;
      end

      // Test 5: Using +: instead of -: (up-select)
      c.data[0][0 +: 8] = 8'hAA;
      if (c.data[0] !== 32'hDEADBEAA) begin
         $display("FAILED: Test 5 - c.data[0] = %h, expected DEADBEAA", c.data[0]);
         pass = 0;
      end

      if (pass)
         $display("PASSED");
   end
endmodule
