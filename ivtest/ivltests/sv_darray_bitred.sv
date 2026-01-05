// Test dynamic array bitwise reduction methods: and, or, xor
module test;
  int arr[];
  int a, o, x;
  int passed = 0;
  int failed = 0;

  initial begin
    // Initialize dynamic array with 4 elements
    arr = new[4];
    arr[0] = 32'hFF00FF00;  // 1111_1111_0000_0000_1111_1111_0000_0000
    arr[1] = 32'hF0F0F0F0;  // 1111_0000_1111_0000_1111_0000_1111_0000
    arr[2] = 32'h0F0F0F0F;  // 0000_1111_0000_1111_0000_1111_0000_1111
    arr[3] = 32'h00FF00FF;  // 0000_0000_1111_1111_0000_0000_1111_1111

    // Test and - bitwise AND of all elements
    // FF00FF00 & F0F0F0F0 = F000F000
    // F000F000 & 0F0F0F0F = 00000000
    // 00000000 & 00FF00FF = 00000000
    a = arr.and;
    if (a == 32'h00000000) begin
      $display("PASSED: and = %h (expected 00000000)", a);
      passed++;
    end else begin
      $display("FAILED: and = %h (expected 00000000)", a);
      failed++;
    end

    // Test or - bitwise OR of all elements
    // FF00FF00 | F0F0F0F0 = FFF0FFF0
    // FFF0FFF0 | 0F0F0F0F = FFFFFFFF
    // FFFFFFFF | 00FF00FF = FFFFFFFF
    o = arr.or;
    if (o == 32'hFFFFFFFF) begin
      $display("PASSED: or = %h (expected FFFFFFFF)", o);
      passed++;
    end else begin
      $display("FAILED: or = %h (expected FFFFFFFF)", o);
      failed++;
    end

    // Test xor - bitwise XOR of all elements
    // FF00FF00 ^ F0F0F0F0 = 0FF00FF0
    // 0FF00FF0 ^ 0F0F0F0F = 00FF00FF
    // 00FF00FF ^ 00FF00FF = 00000000
    x = arr.xor;
    if (x == 32'h00000000) begin
      $display("PASSED: xor = %h (expected 00000000)", x);
      passed++;
    end else begin
      $display("FAILED: xor = %h (expected 00000000)", x);
      failed++;
    end

    // Test with simpler values
    arr = new[3];
    arr[0] = 32'h0000000F;  // bits[3:0] = 1111
    arr[1] = 32'h00000007;  // bits[3:0] = 0111
    arr[2] = 32'h00000003;  // bits[3:0] = 0011

    // and: 1111 & 0111 & 0011 = 0011 = 3
    a = arr.and;
    if (a == 32'h00000003) begin
      $display("PASSED: and with simple values = %h (expected 3)", a);
      passed++;
    end else begin
      $display("FAILED: and with simple values = %h (expected 3)", a);
      failed++;
    end

    // or: 1111 | 0111 | 0011 = 1111 = F
    o = arr.or;
    if (o == 32'h0000000F) begin
      $display("PASSED: or with simple values = %h (expected F)", o);
      passed++;
    end else begin
      $display("FAILED: or with simple values = %h (expected F)", o);
      failed++;
    end

    // xor: 1111 ^ 0111 ^ 0011 = 1000 ^ 0011 = 1011 = B
    x = arr.xor;
    if (x == 32'h0000000B) begin
      $display("PASSED: xor with simple values = %h (expected B)", x);
      passed++;
    end else begin
      $display("FAILED: xor with simple values = %h (expected B)", x);
      failed++;
    end

    // Summary
    $display("\nTotal: %0d passed, %0d failed", passed, failed);
    if (failed == 0)
      $display("ALL TESTS PASSED");
    else
      $display("SOME TESTS FAILED");
  end
endmodule
