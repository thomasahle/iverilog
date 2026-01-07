// Test uvm_config_db with various types including enums

`include "uvm_pkg.sv"

import uvm_pkg::*;

typedef enum bit [1:0] {
  MODE_A = 2'b00,
  MODE_B = 2'b01,
  MODE_C = 2'b10
} test_mode_e;

class my_config extends uvm_object;
  int value;
  function new(string name = "my_config");
    super.new(name);
    value = 100;
  endfunction
endclass

// Simulate agent config with enum property like AXI4
class agent_config extends uvm_object;
  test_mode_e read_data_mode;
  function new(string name = "agent_config");
    super.new(name);
    read_data_mode = MODE_A;
  endfunction
endclass

module test;
  int pass = 1;

  initial begin
    int int_val;
    test_mode_e mode_val;
    my_config cfg_obj;
    my_config cfg_get;
    agent_config agent_cfg_h;

    // Test 1: integer config_db
    uvm_config_db#(int)::set(null, "*", "int_field", 42);
    if (uvm_config_db#(int)::get(null, "", "int_field", int_val)) begin
      if (int_val == 42)
        $display("PASS: int config_db works, got %0d", int_val);
      else begin
        $display("FAIL: int config_db got wrong value %0d, expected 42", int_val);
        pass = 0;
      end
    end else begin
      $display("FAIL: int config_db::get returned 0");
      pass = 0;
    end

    // Test 2: enum config_db (critical for AXI4 AVIP)
    uvm_config_db#(test_mode_e)::set(null, "*", "mode_field", MODE_B);
    if (uvm_config_db#(test_mode_e)::get(null, "", "mode_field", mode_val)) begin
      if (mode_val == MODE_B)
        $display("PASS: enum config_db works, got %s", mode_val.name());
      else begin
        $display("FAIL: enum config_db got wrong value %s, expected MODE_B", mode_val.name());
        pass = 0;
      end
    end else begin
      $display("FAIL: enum config_db::get returned 0");
      pass = 0;
    end

    // Test 2b: enum config_db with class property output (mimics AXI4 pattern)
    agent_cfg_h = new("agent_cfg");
    $display("Before get: agent_cfg_h.read_data_mode = %s", agent_cfg_h.read_data_mode.name());
    uvm_config_db#(test_mode_e)::set(null, "*", "read_data_mode", MODE_C);
    if (uvm_config_db#(test_mode_e)::get(null, "", "read_data_mode", agent_cfg_h.read_data_mode)) begin
      $display("After get: agent_cfg_h.read_data_mode = %s", agent_cfg_h.read_data_mode.name());
      if (agent_cfg_h.read_data_mode == MODE_C)
        $display("PASS: enum config_db to class property works");
      else begin
        $display("FAIL: enum config_db got wrong value in class property: %s, expected MODE_C", agent_cfg_h.read_data_mode.name());
        pass = 0;
      end
    end else begin
      $display("FAIL: enum config_db::get with class property returned 0");
      pass = 0;
    end

    // Test 3: class object config_db
    cfg_obj = new("test_cfg");
    cfg_obj.value = 999;
    uvm_config_db#(my_config)::set(null, "*", "cfg_field", cfg_obj);
    if (uvm_config_db#(my_config)::get(null, "", "cfg_field", cfg_get)) begin
      if (cfg_get != null && cfg_get.value == 999)
        $display("PASS: class config_db works, got value %0d", cfg_get.value);
      else begin
        $display("FAIL: class config_db got wrong object");
        pass = 0;
      end
    end else begin
      $display("FAIL: class config_db::get returned 0");
      pass = 0;
    end

    // Test 4: non-existent field should return 0
    if (uvm_config_db#(int)::get(null, "", "nonexistent", int_val)) begin
      $display("FAIL: config_db should return 0 for nonexistent field");
      pass = 0;
    end else begin
      $display("PASS: config_db returns 0 for nonexistent field");
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
