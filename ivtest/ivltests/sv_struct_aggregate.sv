// Test struct aggregate assignment patterns
// Both named and positional patterns should work correctly

// Unpacked struct
typedef struct {
   int a;
   int b;
   int c;
} unpacked_t;

// Packed struct
typedef struct packed {
   int a;
   int b;
   int c;
} packed_t;

module test;
   int errors = 0;

   initial begin
      unpacked_t u;
      packed_t p;

      // Test 1: Unpacked struct with named aggregate
      u = '{a: 10, b: 20, c: 30};
      if (u.a != 10 || u.b != 20 || u.c != 30) begin
         $display("FAILED Test 1: Unpacked named aggregate: a=%0d, b=%0d, c=%0d", u.a, u.b, u.c);
         errors++;
      end else begin
         $display("PASSED Test 1: Unpacked named aggregate");
      end

      // Test 2: Unpacked struct with positional aggregate
      u = '{100, 200, 300};
      if (u.a != 100 || u.b != 200 || u.c != 300) begin
         $display("FAILED Test 2: Unpacked positional aggregate: a=%0d, b=%0d, c=%0d", u.a, u.b, u.c);
         errors++;
      end else begin
         $display("PASSED Test 2: Unpacked positional aggregate");
      end

      // Test 3: Packed struct with named aggregate
      p = '{a: 11, b: 22, c: 33};
      if (p.a != 11 || p.b != 22 || p.c != 33) begin
         $display("FAILED Test 3: Packed named aggregate: a=%0d, b=%0d, c=%0d", p.a, p.b, p.c);
         errors++;
      end else begin
         $display("PASSED Test 3: Packed named aggregate");
      end

      // Test 4: Packed struct with positional aggregate
      p = '{111, 222, 333};
      if (p.a != 111 || p.b != 222 || p.c != 333) begin
         $display("FAILED Test 4: Packed positional aggregate: a=%0d, b=%0d, c=%0d", p.a, p.b, p.c);
         errors++;
      end else begin
         $display("PASSED Test 4: Packed positional aggregate");
      end

      // Test 5: Named aggregate with out-of-order names
      u = '{c: 3, a: 1, b: 2};
      if (u.a != 1 || u.b != 2 || u.c != 3) begin
         $display("FAILED Test 5: Out-of-order named aggregate: a=%0d, b=%0d, c=%0d", u.a, u.b, u.c);
         errors++;
      end else begin
         $display("PASSED Test 5: Out-of-order named aggregate");
      end

      if (errors == 0)
         $display("PASSED: All struct aggregate tests passed");
      else
         $display("FAILED: %0d errors", errors);

      $finish;
   end
endmodule
