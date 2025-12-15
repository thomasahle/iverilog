// Test queue last element access [$] (SystemVerilog)
// Note: Writing to q[$] (l-value) not yet supported, only reading (r-value)
module test;
  int q[$];
  bit [7:0] bytes[$];

  initial begin
    // Test with int queue
    q.push_back(10);
    q.push_back(20);
    q.push_back(30);

    $display("q[$] = %0d (expected 30)", q[$]);
    if (q[$] !== 30) begin
      $display("FAILED: q[$] = %0d, expected 30", q[$]);
      $finish;
    end

    // Test with byte queue
    bytes.push_back(8'hAA);
    bytes.push_back(8'hBB);
    bytes.push_back(8'hCC);
    if (bytes[$] !== 8'hCC) begin
      $display("FAILED: bytes[$] = %h, expected CC", bytes[$]);
      $finish;
    end

    // Test after pop_back
    q.pop_back();  // Remove 30, now last is 20
    if (q[$] !== 20) begin
      $display("FAILED: q[$] after pop_back = %0d, expected 20", q[$]);
      $finish;
    end

    // Test in expressions
    if (q[0] + q[$] !== 30) begin
      $display("FAILED: q[0] + q[$] = %0d, expected 30", q[0] + q[$]);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
