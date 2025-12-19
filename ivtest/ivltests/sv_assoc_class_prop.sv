// Test associative array as class property - basic operations
module test;

  class Container;
    int data[string];

    function int count();
      return data.num();
    endfunction

    function int has_alpha();
      return data.exists("alpha");
    endfunction

    function int has_beta();
      return data.exists("beta");
    endfunction
  endclass

  Container c;
  int passed;
  int result;

  initial begin
    passed = 1;
    c = new();

    $display("Testing associative array as class property:");

    // Test count on empty array
    result = c.count();
    if (result != 0) begin
      $display("FAILED: count on empty should return 0, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: count on empty = %0d", result);

    // Test exists on empty
    if (c.has_alpha() != 0) begin
      $display("FAILED: has_alpha on empty should return 0");
      passed = 0;
    end else
      $display("PASSED: has_alpha on empty = 0");

    // Add entries via direct property access
    c.data["alpha"] = 100;
    c.data["beta"] = 200;
    c.data["gamma"] = 300;

    // Test count
    result = c.count();
    if (result != 3) begin
      $display("FAILED: count should return 3, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: count() = %0d", result);

    // Test has_alpha
    if (c.has_alpha() != 1) begin
      $display("FAILED: has_alpha should return 1");
      passed = 0;
    end else
      $display("PASSED: has_alpha() = 1");

    // Test has_beta
    if (c.has_beta() != 1) begin
      $display("FAILED: has_beta should return 1");
      passed = 0;
    end else
      $display("PASSED: has_beta() = 1");

    // Test value read via property
    result = c.data["alpha"];
    if (result != 100) begin
      $display("FAILED: data['alpha'] should be 100, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: data['alpha'] = %0d", result);

    // Test value update
    c.data["alpha"] = 111;
    result = c.data["alpha"];
    if (result != 111) begin
      $display("FAILED: data['alpha'] after update should be 111, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: data['alpha'] updated to %0d", result);

    // Test data.num() directly
    result = c.data.num();
    if (result != 3) begin
      $display("FAILED: data.num() should return 3, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: data.num() = %0d", result);

    // Test data.size() directly
    result = c.data.size();
    if (result != 3) begin
      $display("FAILED: data.size() should return 3, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: data.size() = %0d", result);

    $display("");
    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end

endmodule
