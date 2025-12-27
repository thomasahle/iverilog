// Test uvm_config_db wildcard pattern matching with integer type
// Tests patterns like "*", "*env*", etc.

module test;
  int result;
  int passed;

  initial begin
    passed = 1;

    // Test 1: Set with "*" pattern, get with specific path
    uvm_config_db#(int)::set(null, "*", "global_cfg", 42);

    result = 0;
    if (!uvm_config_db#(int)::get(null, "any.path.here", "global_cfg", result)) begin
      $display("FAILED: Test 1 - global config_db::get returned 0");
      passed = 0;
    end else if (result != 42) begin
      $display("FAILED: Test 1 - result=%0d, expected 42", result);
      passed = 0;
    end

    // Test 2: Set with "*env*" pattern
    uvm_config_db#(int)::set(null, "*env*", "env_cfg", 99);

    result = 0;
    if (!uvm_config_db#(int)::get(null, "uvm_test_top.my_env", "env_cfg", result)) begin
      $display("FAILED: Test 2 - env config_db::get returned 0");
      passed = 0;
    end else if (result != 99) begin
      $display("FAILED: Test 2 - result=%0d, expected 99", result);
      passed = 0;
    end

    // Test 3: Pattern shouldn't match different path
    result = 0;
    if (uvm_config_db#(int)::get(null, "uvm_test_top.my_agent", "env_cfg", result)) begin
      $display("FAILED: Test 3 - *env* should not match path without 'env'");
      passed = 0;
    end

    // Test 4: Set with exact path
    uvm_config_db#(int)::set(null, "exact.path", "exact_cfg", 123);

    result = 0;
    if (!uvm_config_db#(int)::get(null, "exact.path", "exact_cfg", result)) begin
      $display("FAILED: Test 4 - exact path config_db::get returned 0");
      passed = 0;
    end else if (result != 123) begin
      $display("FAILED: Test 4 - result=%0d, expected 123", result);
      passed = 0;
    end

    // Test 5: Different field names don't mix
    uvm_config_db#(int)::set(null, "*", "cfg_a", 200);

    result = 0;
    if (uvm_config_db#(int)::get(null, "*", "cfg_b", result)) begin
      $display("FAILED: Test 5 - should not find cfg_b when only cfg_a was set");
      passed = 0;
    end

    if (passed)
      $display("PASSED");
    $finish;
  end
endmodule
