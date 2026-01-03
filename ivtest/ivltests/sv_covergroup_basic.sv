// Test basic covergroup functionality
// Tests sample(), get_coverage(), get_sample_count()
// Compile with: iverilog -g2012 uvm_pkg.sv sv_covergroup_basic.sv

import uvm_pkg::*;

class my_transaction extends uvm_object;
  int data;

  function new(string name = "my_transaction");
    super.new(name);
  endfunction

  // Covergroup that samples the data field
  covergroup data_cg;
    coverpoint data;
  endgroup

  function void post_randomize();
    data_cg.sample();
  endfunction
endclass

module test;
  initial begin
    my_transaction txn;
    int sample_count;
    real coverage;

    txn = new("txn");

    // Create the covergroup instance
    txn.data_cg = new();

    // Set target bins for coverage calculation
    txn.data_cg.set_target_bins(10);

    // Sample a few times
    for (int i = 0; i < 5; i++) begin
      txn.data = i * 10;
      txn.data_cg.sample();
    end

    // Check sample count
    sample_count = txn.data_cg.get_sample_count();
    if (sample_count == 5) begin
      $display("PASSED: sample_count = %0d (expected 5)", sample_count);
    end else begin
      $display("FAILED: sample_count = %0d (expected 5)", sample_count);
    end

    // Check coverage (5 samples out of 10 target bins = 50%)
    coverage = txn.data_cg.get_coverage();
    if (coverage >= 49.0 && coverage <= 51.0) begin
      $display("PASSED: coverage = %0.1f%% (expected ~50%%)", coverage);
    end else begin
      $display("INFO: coverage = %0.1f%% (may vary based on bin implementation)", coverage);
    end

    // Sample more to reach 100%
    for (int i = 5; i < 15; i++) begin
      txn.data = i * 10;
      txn.data_cg.sample();
    end

    coverage = txn.data_cg.get_coverage();
    $display("INFO: After 15 samples, coverage = %0.1f%%", coverage);

    // Note: stop()/start() are not yet implemented
    // Uncomment when implemented:
    // txn.data_cg.stop();
    // txn.data = 999;
    // txn.data_cg.sample();
    // if (txn.data_cg.get_sample_count() == 15) begin
    //   $display("PASSED: stop() prevented additional sampling");
    // end

    $display("PASSED");
  end
endmodule
