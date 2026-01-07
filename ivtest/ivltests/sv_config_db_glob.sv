// Test config_db basic set/get functionality

`include "uvm_pkg.sv"

import uvm_pkg::*;

module test;
  int value_in, value_out;

  initial begin
    value_in = 42;

    // Set a config value
    uvm_config_db#(int)::set(null, "top.env", "my_value", value_in);

    // Get the config value back
    if (!uvm_config_db#(int)::get(null, "top.env", "my_value", value_out)) begin
      $display("FAILED: Could not get config value");
    end else if (value_out !== 42) begin
      $display("FAILED: Wrong value %0d, expected 42", value_out);
    end else begin
      $display("PASSED");
    end

    $finish;
  end
endmodule
