// Test: Unpacked struct member r-value access
// Tests reading from individual members of unpacked structs

module test;
  typedef struct {
    logic [7:0] a;
    logic [15:0] b;
    logic [31:0] c;
  } mystruct_t;

  mystruct_t s;
  logic [7:0] test_a;
  logic [15:0] test_b;
  logic [31:0] test_c;

  initial begin
    // Write to struct members (l-value)
    s.a = 8'hAA;
    s.b = 16'hBBBB;
    s.c = 32'hCCCCCCCC;

    // Read from struct members (r-value)
    test_a = s.a;
    test_b = s.b;
    test_c = s.c;

    // Test in conditional
    if (s.a == 8'hAA && s.b == 16'hBBBB && s.c == 32'hCCCCCCCC) begin
      $display("Conditional check PASSED");
    end else begin
      $display("FAILED: Conditional check failed");
      $display("s.a=%h s.b=%h s.c=%h", s.a, s.b, s.c);
      $finish;
    end

    // Verify values
    if (test_a == 8'hAA && test_b == 16'hBBBB && test_c == 32'hCCCCCCCC) begin
      $display("PASSED");
    end else begin
      $display("FAILED: test_a=%h test_b=%h test_c=%h", test_a, test_b, test_c);
    end
  end
endmodule
