// Test simple associative array with int values
module test;
  int configs[string];
  int errors = 0;

  initial begin
    // Store values
    configs["a"] = 100;
    configs["b"] = 200;

    // Check size
    if (configs.size() != 2) begin
      $display("FAILED: size is %0d, expected 2", configs.size());
      errors++;
    end

    // Check exists
    if (!configs.exists("a")) begin
      $display("FAILED: 'a' should exist");
      errors++;
    end

    // Access value
    if (configs["a"] != 100) begin
      $display("FAILED: configs[a] is %0d, expected 100", configs["a"]);
      errors++;
    end

    // Delete
    configs.delete("a");
    if (configs.size() != 1) begin
      $display("FAILED: size after delete is %0d, expected 1", configs.size());
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
