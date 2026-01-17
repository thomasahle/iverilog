// Test SystemVerilog assignment as expression (SV 11.3.6)
// The value of an assignment expression is the value assigned
module test;
   int a, b, c;
   int arr[4];
   int pass;

   initial begin
      pass = 1;

      // Simple assignment expression
      b = (a = 5);
      if (a !== 5) begin
         $display("FAILED: a should be 5, got %0d", a);
         pass = 0;
      end
      if (b !== 5) begin
         $display("FAILED: b should be 5, got %0d", b);
         pass = 0;
      end

      // Assignment in conditional
      if ((a = 20) > 15) begin
         if (a !== 20) begin
            $display("FAILED: a in conditional should be 20, got %0d", a);
            pass = 0;
         end
      end else begin
         $display("FAILED: conditional with assignment expression");
         pass = 0;
      end

      // Assignment to array element
      arr[0] = 0;
      b = (arr[0] = 100);
      if (arr[0] !== 100) begin
         $display("FAILED: arr[0] should be 100, got %0d", arr[0]);
         pass = 0;
      end
      if (b !== 100) begin
         $display("FAILED: b from array assign should be 100, got %0d", b);
         pass = 0;
      end

      // Use in arithmetic
      a = 5;
      b = (a = 3) + 2;
      if (a !== 3) begin
         $display("FAILED: a should be 3, got %0d", a);
         pass = 0;
      end
      if (b !== 5) begin
         $display("FAILED: b should be 3+2=5, got %0d", b);
         pass = 0;
      end

      if (pass) begin
         $display("PASSED");
      end
   end
endmodule
