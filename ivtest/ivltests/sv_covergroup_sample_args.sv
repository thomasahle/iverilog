// Test covergroup with function sample arguments in class
// Verifies: covergroup with sample(args) can pass arguments to coverpoints
`include "uvm_pkg.sv"
import uvm_pkg::*;

class Transaction extends uvm_object;
  rand bit [1:0] cmd;
  rand bit [7:0] addr;

  `uvm_object_utils(Transaction)

  function new(string name = "Transaction");
    super.new(name);
  endfunction
endclass

class Coverage extends uvm_object;
  // Covergroup with sample function taking argument
  covergroup TransactionCoverage with function sample(Transaction tx);
    CMD_CP: coverpoint tx.cmd;
    ADDR_CP: coverpoint tx.addr;
  endgroup

  `uvm_object_utils(Coverage)

  function new(string name = "Coverage");
    super.new(name);
    TransactionCoverage = new();
  endfunction
endclass

module test;
  initial begin
    Coverage cov;
    Transaction tx;
    int i;

    cov = new("cov");
    tx = new("tx");

    // Sample several transactions
    for (i = 0; i < 20; i++) begin
      if (!tx.randomize()) begin
        $display("FAILED: randomize failed");
        $finish;
      end
      cov.TransactionCoverage.sample(tx);
    end

    $display("Sample count: %0d", cov.TransactionCoverage.get_sample_count());
    if (cov.TransactionCoverage.get_sample_count() != 20) begin
      $display("FAILED: Expected 20 samples, got %0d", cov.TransactionCoverage.get_sample_count());
      $finish;
    end

    $display("Coverage: %0.2f%%", cov.TransactionCoverage.get_coverage());

    $display("Covergroup with sample arguments working");
    $display("PASSED");
    $finish;
  end

endmodule
