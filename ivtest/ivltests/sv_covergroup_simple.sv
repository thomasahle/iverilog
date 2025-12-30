// Simple test for covergroup functionality
// Tests sample() and get_coverage() with UVM package

// Import UVM for __ivl_covergroup
import uvm_pkg::*;

class DataItem extends uvm_object;
  int value;
  bit[7:0] addr;

  function new(string name = "DataItem");
    super.new(name);
    value = 0;
    addr = 0;
  endfunction
endclass

class CoverageCollector extends uvm_object;
  // Covergroup with sample function
  covergroup data_cg with function sample(DataItem item);
    VALUE_CP: coverpoint item.value {
      bins low = {[0:100]};
      bins high = {[101:$]};
    }

    ADDR_CP: coverpoint item.addr {
      bins addrs[] = {[0:255]};
    }
  endgroup

  function new(string name = "CoverageCollector");
    super.new(name);
    data_cg = new();
  endfunction

  function void collect(DataItem item);
    data_cg.sample(item);
  endfunction

  function real get_cov();
    return data_cg.get_coverage();
  endfunction
endclass

module test;
  CoverageCollector cov;
  DataItem item;
  real coverage_val;
  int passed;

  initial begin
    passed = 1;

    // Create collector and item
    cov = new("cov");
    item = new("item");

    // Initial coverage should be 0
    coverage_val = cov.get_cov();
    $display("Initial coverage: %0.2f%%", coverage_val);
    if (coverage_val != 0.0) begin
      $display("FAILED: Expected initial coverage 0.0, got %0.2f", coverage_val);
      passed = 0;
    end

    // Sample some data
    for (int i = 0; i < 20; i++) begin
      item.value = i * 10;
      item.addr = i * 5;
      cov.collect(item);
    end

    // Coverage should be non-zero after sampling
    coverage_val = cov.get_cov();
    $display("After 20 samples, coverage: %0.2f%%", coverage_val);
    if (coverage_val <= 0.0) begin
      $display("FAILED: Expected non-zero coverage after sampling");
      passed = 0;
    end

    // Sample more to increase coverage
    for (int i = 0; i < 100; i++) begin
      item.value = i;
      item.addr = i;
      cov.collect(item);
    end

    // Coverage should increase with more samples
    coverage_val = cov.get_cov();
    $display("After 120 samples, coverage: %0.2f%%", coverage_val);
    if (coverage_val < 50.0) begin
      $display("FAILED: Expected higher coverage after many samples");
      passed = 0;
    end

    if (passed)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end
endmodule
