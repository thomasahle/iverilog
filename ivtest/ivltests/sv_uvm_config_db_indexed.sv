// Test config_db with $sformatf key
// Based on APB AVIP pattern: config_db::set(this, "*", $sformatf("key[%0d]", i), val)
`include "uvm_pkg.sv"

import uvm_pkg::*;

module test;
  int vals[3];
  int pass = 1;

  initial begin
    int get_val;

    // Set multiple values with indexed keys
    for (int i = 0; i < 3; i++) begin
      vals[i] = 100 + i * 10;
      uvm_config_db#(int)::set(null, "*", $sformatf("config[%0d]", i), vals[i]);
    end

    // Get them back
    for (int i = 0; i < 3; i++) begin
      if (uvm_config_db#(int)::get(null, "", $sformatf("config[%0d]", i), get_val)) begin
        if (get_val == vals[i])
          $display("PASS: config[%0d] = %0d", i, get_val);
        else begin
          $display("FAIL: config[%0d] = %0d, expected %0d", i, get_val, vals[i]);
          pass = 0;
        end
      end else begin
        $display("FAIL: config[%0d] not found", i);
        pass = 0;
      end
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
