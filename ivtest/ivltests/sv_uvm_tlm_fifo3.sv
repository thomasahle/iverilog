// Test parameterized class variable declaration at module level
// This pattern is NOT supported due to LALR(1) grammar conflict:
//   ClassName#(type) var; looks like interface instantiation
//
// WORKAROUND: Use package scope: pkg::ClassName#(type) var;
//
// This test documents the limitation and workaround.

`include "uvm_pkg.sv"

package test_pkg;
  import uvm_pkg::*;

  // Simple parameterized container class
  class Container #(type T = int);
    T data[$];

    function void push(T item);
      data.push_back(item);
    endfunction

    function T pop();
      return data.pop_front();
    endfunction

    function int size();
      return data.size();
    endfunction
  endclass

endpackage

module test;
  import uvm_pkg::*;
  import test_pkg::*;

  // WORKAROUND: Use package-scoped type
  // This works: pkg::Container#(int) fifo;
  test_pkg::Container#(int) int_fifo;

  // Direct parameterized class at module level would conflict with
  // interface instantiation syntax:
  // Container#(int) fifo;  // ERROR - looks like interface inst

  initial begin
    // Test the workaround
    int_fifo = new();

    int_fifo.push(10);
    int_fifo.push(20);
    int_fifo.push(30);

    if (int_fifo.size() != 3) begin
      $display("FAILED: Expected size 3, got %0d", int_fifo.size());
      $finish;
    end

    if (int_fifo.pop() != 10) begin
      $display("FAILED: First pop should return 10");
      $finish;
    end

    if (int_fifo.pop() != 20) begin
      $display("FAILED: Second pop should return 20");
      $finish;
    end

    $display("Workaround test passed: pkg::Container#(int) works at module level");
    $display("PASSED");
    $finish;
  end
endmodule
