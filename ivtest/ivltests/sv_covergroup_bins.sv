// Test for covergroup bins parsing
// Tests that coverpoints and bins are correctly parsed
// Note: Actual bin tracking not yet implemented - just tests parsing

`include "uvm_pkg.sv"
import uvm_pkg::*;

class test_coverage extends uvm_object;
  `uvm_object_utils(test_coverage)

  bit [7:0] addr;
  bit [3:0] cmd;

  // Covergroup with explicit bins
  covergroup addr_cg;
    addr_cp: coverpoint addr {
      bins low = {[0:63]};
      bins mid = {[64:127]};
      bins high = {[128:191]};
      bins very_high = {[192:255]};
    }
    cmd_cp: coverpoint cmd {
      bins read = {4'h1};
      bins write = {4'h2};
      bins burst = {[4'h3:4'h7]};
      ignore_bins reserved = {[4'h8:4'hF]};
    }
  endgroup

  function new(string name = "test_coverage");
    super.new(name);
    addr_cg = new();
  endfunction

  function void sample_data(bit [7:0] a, bit [3:0] c);
    addr = a;
    cmd = c;
    addr_cg.sample();
  endfunction
endclass

module test;
  initial begin
    test_coverage tc = new("tc");

    // Sample some data
    tc.sample_data(32, 1);   // low addr, read cmd
    tc.sample_data(100, 2);  // mid addr, write cmd
    tc.sample_data(200, 5);  // very_high addr, burst cmd

    $display("Samples: %0d", tc.addr_cg.get_sample_count());
    $display("PASSED - Covergroup with bins parsed correctly");
    $finish;
  end
endmodule
