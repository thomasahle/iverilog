// Test unpacked struct support
module test;
  // Unpacked struct (no 'packed' keyword)
  typedef struct {
    int a;
    logic [7:0] b;
    int c;
  } unpacked_s;

  initial begin
    unpacked_s s;
    int pass_count = 0;
    int fail_count = 0;

    // Test member assignment
    s.a = 42;
    s.b = 8'hFF;
    s.c = 100;

    // Test member access
    if (s.a == 42) pass_count++; else begin fail_count++; $display("FAIL: s.a=%0d, expected 42", s.a); end
    if (s.b == 8'hFF) pass_count++; else begin fail_count++; $display("FAIL: s.b=%0h, expected FF", s.b); end
    if (s.c == 100) pass_count++; else begin fail_count++; $display("FAIL: s.c=%0d, expected 100", s.c); end

    // Test modification
    s.a = s.a + 8;
    if (s.a == 50) pass_count++; else begin fail_count++; $display("FAIL: s.a=%0d, expected 50", s.a); end

    // Test struct copy
    begin
      unpacked_s s2;
      s2 = s;
      if (s2.a == s.a) pass_count++; else begin fail_count++; $display("FAIL: copy s.a"); end
      if (s2.b == s.b) pass_count++; else begin fail_count++; $display("FAIL: copy s.b"); end
      if (s2.c == s.c) pass_count++; else begin fail_count++; $display("FAIL: copy s.c"); end
    end

    if (fail_count == 0)
      $display("PASSED: All %0d unpacked struct tests passed", pass_count);
    else
      $display("FAILED: %0d failures, %0d passes", fail_count, pass_count);
  end
endmodule
