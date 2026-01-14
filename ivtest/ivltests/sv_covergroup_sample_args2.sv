// Test covergroup with sample arguments (parameterized covergroup)
// This tests that coverage tracking works even when sample() is called
// with arguments, which is the common UVM pattern.

`include "uvm_pkg.sv"

module test;
  import uvm_pkg::*;

  // Simple config class
  class my_config;
    int addr;
  endclass

  // Simple transaction class
  class my_tx;
    int data;
    int addr;
  endclass

  // Coverage collector with parameterized covergroup
  class tx_coverage;
    covergroup cg with function sample(my_config cfg, my_tx tx);
      option.per_instance = 1;
      DATA_CP: coverpoint tx.data;
      ADDR_CP: coverpoint cfg.addr;
    endgroup

    function new();
      cg = new();
    endfunction

    function void sample_tx(my_config cfg, my_tx tx);
      cg.sample(cfg, tx);
    endfunction

    function int get_count();
      return cg.get_sample_count();
    endfunction

    function real get_cov();
      return cg.get_coverage();
    endfunction
  endclass

  tx_coverage cov;
  my_config cfg;
  my_tx tx;

  initial begin
    cov = new();
    cfg = new();
    tx = new();

    // Sample some values
    for (int i = 0; i < 10; i++) begin
      cfg.addr = i * 100;
      tx.data = i * 10;
      cov.sample_tx(cfg, tx);
    end

    $display("Sample count: %0d", cov.get_count());
    $display("Coverage: %0.2f%%", cov.get_cov());

    // Verify sample count
    if (cov.get_count() != 10) begin
      $display("FAILED: Expected sample count 10, got %0d", cov.get_count());
      $finish;
    end

    // Verify coverage is non-zero (each sample should contribute to coverage)
    if (cov.get_cov() <= 0.0) begin
      $display("FAILED: Expected non-zero coverage, got %0.2f%%", cov.get_cov());
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
