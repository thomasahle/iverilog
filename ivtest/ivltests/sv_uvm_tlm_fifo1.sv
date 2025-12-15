// Test uvm_tlm_analysis_fifo basic functionality
// This tests the stub implementation that counts writes
// Note: Simplified test to avoid VVP object parameter limitations

// Include UVM package directly for Icarus
`include "uvm_pkg.sv"

module test;
  import uvm_pkg::*;

  // Use default type parameter (uvm_object)
  uvm_tlm_analysis_fifo #(uvm_object) fifo;
  int errors = 0;

  initial begin
    // Create FIFO
    fifo = new("fifo", null);

    // Check initial state
    if (fifo.size() !== 0) begin
      $display("FAILED: Initial size should be 0, got %0d", fifo.size());
      errors++;
    end

    if (!fifo.is_empty()) begin
      $display("FAILED: FIFO should be empty initially");
      errors++;
    end

    // Test used() method (should match size for stub)
    if (fifo.used() !== 0) begin
      $display("FAILED: used() should return 0, got %0d", fifo.used());
      errors++;
    end

    // Test flush on empty
    fifo.flush();
    if (fifo.size() !== 0) begin
      $display("FAILED: Size should still be 0 after flush, got %0d", fifo.size());
      errors++;
    end

    // Note: Cannot test write() directly due to VVP object parameter limitations
    // The write functionality is tested by actual UVM testbenches like DDR3

    if (errors == 0)
      $display("PASSED");

    $finish;
  end
endmodule
