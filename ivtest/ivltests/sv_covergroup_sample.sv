// Test covergroup sample() method invocation with typed arguments
// This tests that covergroup sample() calls compile correctly
// even when the covergroup stub class doesn't know about specific argument types

class transaction;
  bit [7:0] data;
  bit [3:0] addr;
endclass

class coverage;
  covergroup cg with function sample(transaction t);
    option.per_instance = 1;
    DATA_CP : coverpoint t.data {
      bins LOW = {[0:127]};
      bins HIGH = {[128:255]};
    }
  endgroup

  function new();
    cg = new();
  endfunction

  function void collect(transaction t);
    // This is where the covergroup sample() is called with typed argument
    cg.sample(t);
  endfunction
endclass

module test;
  coverage cov;
  transaction txn;

  initial begin
    cov = new();
    txn = new();
    txn.data = 8'h55;
    txn.addr = 4'h3;
    cov.collect(txn);
    $display("PASSED: covergroup sample() with typed argument compiles");
  end
endmodule
