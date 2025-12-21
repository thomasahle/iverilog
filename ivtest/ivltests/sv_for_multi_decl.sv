// Test multiple variable declarations in for loop init
// IEEE 1800-2017: for (int i = 0, j = 10; condition; step)

module test;
  integer errors;

  initial begin
    errors = 0;

    // Test basic multiple variable declaration
    begin
      int sum_i, sum_j;
      sum_i = 0;
      sum_j = 0;
      for (int i = 0, j = 10; i < 5; i = i + 1) begin
        sum_i = sum_i + i;
        sum_j = sum_j + j;
        j = j - 1;
      end
      // i: 0+1+2+3+4 = 10
      // j: 10+9+8+7+6 = 40
      if (sum_i !== 10) begin
        $display("FAILED: sum_i = %0d, expected 10", sum_i);
        errors = errors + 1;
      end
      if (sum_j !== 40) begin
        $display("FAILED: sum_j = %0d, expected 40", sum_j);
        errors = errors + 1;
      end
    end

    // Test with three variables
    begin
      int product;
      product = 1;
      for (int a = 1, b = 2, c = 3; a <= 3; a = a + 1) begin
        product = product * (a + b + c);
        b = b + 1;
        c = c + 1;
      end
      // iteration 1: a=1, b=2, c=3, sum=6, product=6
      // iteration 2: a=2, b=3, c=4, sum=9, product=54
      // iteration 3: a=3, b=4, c=5, sum=12, product=648
      if (product !== 648) begin
        $display("FAILED: product = %0d, expected 648", product);
        errors = errors + 1;
      end
    end

    // Test that variables are properly scoped
    begin
      int x;
      x = 100;
      for (int i = 0, x = 0; i < 3; i = i + 1) begin
        x = x + i;
      end
      // Inner x should be 0+1+2 = 3, but outer x should still be 100
      if (x !== 100) begin
        $display("FAILED: x = %0d, expected 100", x);
        errors = errors + 1;
      end
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED with %0d errors", errors);
  end
endmodule
