// Simple covergroup test
`include "uvm_pkg.sv"
import uvm_pkg::*;

class simple_test extends uvm_object;
  int data;

  // Covergroup declaration
  covergroup my_cg;
    coverpoint data;
  endgroup

  function new(string name = "simple_test");
    super.new(name);
    // Create the covergroup
    my_cg = new();
  endfunction
endclass

module test;
  initial begin
    simple_test t;
    t = new("t");

    $display("Initial sample_count = %0d", t.my_cg.get_sample_count());

    // Sample a few times
    t.data = 1;
    t.my_cg.sample();
    $display("After 1 sample, count = %0d", t.my_cg.get_sample_count());

    t.data = 2;
    t.my_cg.sample();
    $display("After 2 samples, count = %0d", t.my_cg.get_sample_count());

    t.data = 3;
    t.my_cg.sample();
    $display("After 3 samples, count = %0d", t.my_cg.get_sample_count());

    if (t.my_cg.get_sample_count() == 3) begin
      $display("PASSED: Coverage tracking working!");
    end else begin
      $display("FAILED: Expected 3 samples, got %0d", t.my_cg.get_sample_count());
    end
  end
endmodule
