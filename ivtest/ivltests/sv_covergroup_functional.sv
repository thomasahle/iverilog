// Test covergroup functionality with UVM-style patterns
// Tests sample() and get_coverage() with UVM base classes

// Import UVM package
import uvm_pkg::*;

class Transaction extends uvm_object;
  rand int data;
  rand bit[7:0] addr;

  function new(string name = "Transaction");
    super.new(name);
  endfunction
endclass

class MyConfig extends uvm_object;
  int mode;

  function new(string name = "MyConfig");
    super.new(name);
    mode = 0;
  endfunction
endclass

// Covergroup inside a class (typical UVM pattern)
class MyCoverage extends uvm_component;
  // Covergroup with sample function
  covergroup cg with function sample(MyConfig cfg, Transaction txn);
    // Coverpoints (parsed but bin tracking is simplified)
    option.per_instance = 1;

    DATA_CP: coverpoint txn.data {
      bins low = {[0:255]};
      bins high = {[256:$]};
    }

    ADDR_CP: coverpoint txn.addr {
      bins all_addrs[] = {[0:255]};
    }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    cg = new();
  endfunction

  function void sample_transaction(MyConfig cfg, Transaction txn);
    cg.sample(cfg, txn);
  endfunction

  function real report_coverage();
    return cg.get_coverage();
  endfunction
endclass

module test;
  MyCoverage cov;
  MyConfig cfg;
  Transaction txn;
  real coverage_val;
  int passed;

  initial begin
    passed = 1;

    // Create objects
    cov = new("cov", null);
    cfg = new("cfg");
    txn = new("txn");

    // Initial coverage should be 0
    coverage_val = cov.report_coverage();
    $display("Initial coverage: %0.2f%%", coverage_val);
    if (coverage_val != 0.0) begin
      $display("FAILED: Expected initial coverage 0.0, got %0.2f", coverage_val);
      passed = 0;
    end

    // Sample some transactions
    for (int i = 0; i < 20; i++) begin
      txn.data = i * 100;
      txn.addr = i * 10;
      cov.sample_transaction(cfg, txn);
    end

    // Coverage should be non-zero after sampling
    coverage_val = cov.report_coverage();
    $display("After 20 samples, coverage: %0.2f%%", coverage_val);
    if (coverage_val <= 0.0) begin
      $display("FAILED: Expected non-zero coverage after sampling");
      passed = 0;
    end

    // Sample more to increase coverage
    for (int i = 0; i < 100; i++) begin
      txn.data = i;
      txn.addr = i;
      cov.sample_transaction(cfg, txn);
    end

    // Coverage should be high with many samples
    coverage_val = cov.report_coverage();
    $display("After 120 samples, coverage: %0.2f%%", coverage_val);

    if (passed)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end
endmodule
