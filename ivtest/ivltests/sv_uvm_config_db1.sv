// Test uvm_config_db basic operations with integers
// Tests set and get of integer values

`include "uvm_pkg.sv"

module test;
  import uvm_pkg::*;

  int int_val;
  int int_val2;
  bit result;

  initial begin
    // Test integer config_db set and get
    uvm_config_db#(int)::set(null, "*", "timeout", 1000);

    result = uvm_config_db#(int)::get(null, "", "timeout", int_val);
    if (!result) begin
      $display("FAILED: config_db::get for timeout returned 0");
      $finish;
    end
    if (int_val != 1000) begin
      $display("FAILED: timeout = %0d, expected 1000", int_val);
      $finish;
    end

    // Test multiple keys
    uvm_config_db#(int)::set(null, "*", "max_count", 500);
    result = uvm_config_db#(int)::get(null, "", "max_count", int_val2);
    if (!result || int_val2 != 500) begin
      $display("FAILED: max_count = %0d, expected 500", int_val2);
      $finish;
    end

    // Test overwriting a value
    uvm_config_db#(int)::set(null, "*", "timeout", 2000);
    result = uvm_config_db#(int)::get(null, "", "timeout", int_val);
    if (int_val != 2000) begin
      $display("FAILED: overwritten timeout = %0d, expected 2000", int_val);
      $finish;
    end

    // Verify other key wasn't affected
    result = uvm_config_db#(int)::get(null, "", "max_count", int_val2);
    if (int_val2 != 500) begin
      $display("FAILED: max_count was corrupted, got %0d", int_val2);
      $finish;
    end

    // Test getting non-existent key (should return 0)
    result = uvm_config_db#(int)::get(null, "", "nonexistent", int_val);
    if (result) begin
      $display("FAILED: get for nonexistent key should return 0");
      $finish;
    end

    $display("PASSED");
  end
endmodule
