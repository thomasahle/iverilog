// Test for named struct aggregate assignment patterns (part 2)
// Tests complex named aggregate patterns including nested structs,
// default values, and mixed named/positional patterns

module test;

  // Simple struct
  typedef struct packed {
    logic [7:0] a;
    logic [7:0] b;
    logic [7:0] c;
  } simple_t;

  // Nested struct
  typedef struct packed {
    logic [7:0] header;
    simple_t payload;
    logic [7:0] footer;
  } nested_t;

  // Struct with array member
  typedef struct packed {
    logic [3:0][7:0] data;
    logic [7:0] checksum;
  } array_member_t;

  simple_t s1, s2;
  nested_t n1;
  array_member_t arr1;
  int errors = 0;

  initial begin
    // Test 1: Named assignment pattern with reordered members
    s1 = '{c: 8'h33, a: 8'h11, b: 8'h22};
    if (s1.a !== 8'h11 || s1.b !== 8'h22 || s1.c !== 8'h33) begin
      $display("FAILED: Test 1 - Named pattern with reordering");
      $display("  Expected: a=11, b=22, c=33");
      $display("  Got: a=%h, b=%h, c=%h", s1.a, s1.b, s1.c);
      errors++;
    end else begin
      $display("PASSED: Test 1 - Named pattern with reordering");
    end

    // Test 2: Named assignment with all members
    s2 = '{b: 8'hBB, c: 8'hCC, a: 8'hAA};
    if (s2.a !== 8'hAA || s2.b !== 8'hBB || s2.c !== 8'hCC) begin
      $display("FAILED: Test 2 - Named pattern all members");
      $display("  Expected: a=AA, b=BB, c=CC");
      $display("  Got: a=%h, b=%h, c=%h", s2.a, s2.b, s2.c);
      errors++;
    end else begin
      $display("PASSED: Test 2 - Named pattern all members");
    end

    // Test 3: Nested struct with named patterns
    n1 = '{header: 8'hAA, payload: '{a: 8'h11, b: 8'h22, c: 8'h33}, footer: 8'hBB};
    if (n1.header !== 8'hAA || n1.payload.a !== 8'h11 ||
        n1.payload.b !== 8'h22 || n1.payload.c !== 8'h33 ||
        n1.footer !== 8'hBB) begin
      $display("FAILED: Test 3 - Nested named pattern");
      $display("  Expected: header=AA, payload.a=11, payload.b=22, payload.c=33, footer=BB");
      $display("  Got: header=%h, payload.a=%h, payload.b=%h, payload.c=%h, footer=%h",
               n1.header, n1.payload.a, n1.payload.b, n1.payload.c, n1.footer);
      errors++;
    end else begin
      $display("PASSED: Test 3 - Nested named pattern");
    end

    // Test 4: Array member with named pattern
    arr1 = '{data: '{8'h44, 8'h33, 8'h22, 8'h11}, checksum: 8'hAA};
    if (arr1.checksum !== 8'hAA || arr1.data[0] !== 8'h11 ||
        arr1.data[1] !== 8'h22 || arr1.data[2] !== 8'h33 ||
        arr1.data[3] !== 8'h44) begin
      $display("FAILED: Test 4 - Array member named pattern");
      $display("  Expected: data[0]=11, data[1]=22, data[2]=33, data[3]=44, checksum=AA");
      $display("  Got: data[0]=%h, data[1]=%h, data[2]=%h, data[3]=%h, checksum=%h",
               arr1.data[0], arr1.data[1], arr1.data[2], arr1.data[3], arr1.checksum);
      errors++;
    end else begin
      $display("PASSED: Test 4 - Array member named pattern");
    end

    // Final result
    if (errors == 0) begin
      $display("PASSED");
    end else begin
      $display("FAILED: %0d test(s) failed", errors);
    end
  end

endmodule
