// Test config_db wildcard pattern matching with simple int values
// This tests the fallback matching for wildcards like "*"

`include "uvm_macros.svh"
import uvm_pkg::*;

module test;
  int value_in, value_out;
  int errors = 0;

  initial begin
    value_in = 123;

    // Test 1: Set with wildcard "*" pattern, get with empty inst_name
    // This simulates UVM's typical usage pattern:
    //   set(this, "*", "field", value)  // from test
    //   get(this, "", "field", dest)    // from env
    uvm_config_db#(int)::set(null, "*", "test_config", value_in);

    value_out = 0;
    if (!uvm_config_db#(int)::get(null, "", "test_config", value_out)) begin
      $display("FAILED: Test 1 - Could not get config with wildcard pattern");
      errors++;
    end else if (value_out !== 123) begin
      $display("FAILED: Test 1 - Wrong value %0d, expected 123", value_out);
      errors++;
    end else begin
      $display("PASSED: Test 1 - Wildcard pattern match");
    end

    // Test 2: Set with specific pattern "*env*", get with matching path
    value_in = 456;
    uvm_config_db#(int)::set(null, "*env*", "env_config", value_in);

    value_out = 0;
    if (!uvm_config_db#(int)::get(null, "my_env", "env_config", value_out)) begin
      $display("FAILED: Test 2 - Could not get config with *env* pattern");
      errors++;
    end else if (value_out !== 456) begin
      $display("FAILED: Test 2 - Wrong value %0d, expected 456", value_out);
      errors++;
    end else begin
      $display("PASSED: Test 2 - Pattern *env* matches my_env");
    end

    // Summary
    if (errors == 0) begin
      $display("PASSED");
    end else begin
      $display("FAILED: %0d test(s) failed", errors);
    end

    $finish;
  end
endmodule
