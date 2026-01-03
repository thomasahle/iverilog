// Test queue array methods: min, max, sum, unique
// Note: find() with 'with' clause is not yet supported
module test;
  int q[$] = '{30, 10, 40, 20, 30};
  int result[$];
  int val;
  int errors = 0;

  initial begin
    // Test min()
    result = q.min();
    if (result.size() != 1 || result[0] != 10) begin
      $display("FAILED: min result is %p, expected {10}", result);
      errors++;
    end

    // Test max()
    result = q.max();
    if (result.size() != 1 || result[0] != 40) begin
      $display("FAILED: max result is %p, expected {40}", result);
      errors++;
    end

    // Test sum()
    val = q.sum();
    if (val != 130) begin
      $display("FAILED: sum is %0d, expected 130", val);
      errors++;
    end

    // Test unique()
    result = q.unique();
    if (result.size() != 4) begin
      $display("FAILED: unique size is %0d, expected 4", result.size());
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
