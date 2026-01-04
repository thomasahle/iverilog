// Test string atooct() and atobin() methods
module test;
  string s;
  int v;
  int pass_count = 0;
  int fail_count = 0;

  initial begin
    // Test atooct - octal conversion
    s = "377";
    v = s.atooct();
    if (v == 255) begin
      $display("PASS: atooct('377') = 255");
      pass_count++;
    end else begin
      $display("FAIL: atooct('377') expected 255, got %0d", v);
      fail_count++;
    end

    s = "10";
    v = s.atooct();
    if (v == 8) begin
      $display("PASS: atooct('10') = 8");
      pass_count++;
    end else begin
      $display("FAIL: atooct('10') expected 8, got %0d", v);
      fail_count++;
    end

    // Test atobin - binary conversion
    s = "11111111";
    v = s.atobin();
    if (v == 255) begin
      $display("PASS: atobin('11111111') = 255");
      pass_count++;
    end else begin
      $display("FAIL: atobin('11111111') expected 255, got %0d", v);
      fail_count++;
    end

    s = "1010";
    v = s.atobin();
    if (v == 10) begin
      $display("PASS: atobin('1010') = 10");
      pass_count++;
    end else begin
      $display("FAIL: atobin('1010') expected 10, got %0d", v);
      fail_count++;
    end

    // Test with underscores
    s = "1111_1111";
    v = s.atobin();
    if (v == 255) begin
      $display("PASS: atobin('1111_1111') = 255");
      pass_count++;
    end else begin
      $display("FAIL: atobin('1111_1111') expected 255, got %0d", v);
      fail_count++;
    end

    // Summary
    if (fail_count == 0) begin
      $display("PASSED: All %0d tests passed", pass_count);
    end else begin
      $display("FAILED: %0d passed, %0d failed", pass_count, fail_count);
    end
  end
endmodule
