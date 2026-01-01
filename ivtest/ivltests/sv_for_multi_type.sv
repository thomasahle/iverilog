// Test multi-type variable declarations in for loop
// e.g., for(int j=0, int loc=0; ...)
module test;
  initial begin
    // Test multi-type for loop initializer
    for(int j=0, int loc=0; j<5; j++) begin
      if (j == 0 && loc !== 0) begin
        $display("FAILED: loc should be 0, got %0d", loc);
        $finish;
      end
    end

    // Test 3 variables with repeated types
    for(int a=1, int b=2, int c=3; a<3; a++) begin
      if (a == 1 && b !== 2) begin
        $display("FAILED: b should be 2, got %0d", b);
        $finish;
      end
      if (a == 1 && c !== 3) begin
        $display("FAILED: c should be 3, got %0d", c);
        $finish;
      end
    end

    $display("PASSED");
  end
endmodule
