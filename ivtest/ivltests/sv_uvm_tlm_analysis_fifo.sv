// Test TLM analysis port -> export -> FIFO forwarding
// This tests the full chain: analysis_port.write() -> export.tlm_write() -> FIFO.write()

// Note: uvm_pkg.sv must be compiled first on the command line
import uvm_pkg::*;

// Simple transaction class
class my_transaction extends uvm_object;
  int addr;
  int data;

  function new(string name = "my_transaction");
    super.new(name);
    addr = 0;
    data = 0;
  endfunction

  virtual function string get_type_name();
    return "my_transaction";
  endfunction
endclass

module test;
  initial begin
    uvm_analysis_port#(my_transaction) port;
    uvm_tlm_analysis_fifo#(my_transaction) fifo;
    my_transaction tx, rx;
    int pass_count = 0;

    // Create port and FIFO
    port = new("port", null);
    fifo = new("fifo", null);

    // Connect port to FIFO's export
    port.connect(fifo.analysis_export);

    // Create and write transaction
    tx = new("tx");
    tx.addr = 32'h1234;
    tx.data = 32'hABCD;

    $display("Writing transaction: addr=0x%h, data=0x%h", tx.addr, tx.data);
    port.write(tx);

    // Check FIFO has data
    if (fifo.size() != 1) begin
      $display("FAIL: FIFO size=%0d, expected 1", fifo.size());
      $finish;
    end
    $display("FIFO size after write: %0d", fifo.size());
    pass_count++;

    // Try to get the transaction
    if (!fifo.try_get(rx)) begin
      $display("FAIL: try_get returned false");
      $finish;
    end
    pass_count++;

    // Verify data
    if (rx.addr !== tx.addr) begin
      $display("FAIL: addr mismatch: got 0x%h, expected 0x%h", rx.addr, tx.addr);
      $finish;
    end
    pass_count++;

    if (rx.data !== tx.data) begin
      $display("FAIL: data mismatch: got 0x%h, expected 0x%h", rx.data, tx.data);
      $finish;
    end
    pass_count++;

    // FIFO should be empty now
    if (fifo.size() != 0) begin
      $display("FAIL: FIFO size=%0d after get, expected 0", fifo.size());
      $finish;
    end
    pass_count++;

    // Test multiple transactions
    for (int i = 0; i < 5; i++) begin
      tx = new($sformatf("tx%0d", i));
      tx.addr = i * 100;
      tx.data = i * 1000;
      port.write(tx);
    end

    if (fifo.size() != 5) begin
      $display("FAIL: FIFO size=%0d after 5 writes, expected 5", fifo.size());
      $finish;
    end
    pass_count++;

    // Read all back and verify
    for (int i = 0; i < 5; i++) begin
      if (!fifo.try_get(rx)) begin
        $display("FAIL: try_get %0d returned false", i);
        $finish;
      end
      if (rx.addr !== i * 100) begin
        $display("FAIL: multi-tx addr mismatch at %0d: got %0d, expected %0d", i, rx.addr, i * 100);
        $finish;
      end
      if (rx.data !== i * 1000) begin
        $display("FAIL: multi-tx data mismatch at %0d: got %0d, expected %0d", i, rx.data, i * 1000);
        $finish;
      end
    end
    pass_count++;

    if (pass_count == 7) begin
      $display("PASSED: TLM analysis_port -> export -> FIFO chain works correctly");
    end else begin
      $display("FAIL: Only %0d of 7 tests passed", pass_count);
    end
  end
endmodule
