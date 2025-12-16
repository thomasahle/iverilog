// Test const ref in class methods
// IEEE 1800-2005: const ref in class member functions

module test;

  // Simple struct type
  typedef struct packed {
    logic [31:0] addr;
    logic [31:0] data;
  } tx_t;

  // Class with methods using const ref
  class adapter;
    // Method with const ref argument
    function automatic int process(const ref tx_t tx);
      return tx.addr + tx.data;
    endfunction

    // Method with const ref and other args
    task automatic display(const ref tx_t tx, input string prefix);
      $display("%s: addr=%0h data=%0h", prefix, tx.addr, tx.data);
    endtask
  endclass

  adapter adp;
  tx_t my_tx;
  int result;

  initial begin
    adp = new();
    my_tx.addr = 32'h2000;
    my_tx.data = 32'h100;

    // Test const ref in class method
    result = adp.process(my_tx);
    if (result !== 32'h2100) begin
      $display("FAILED: process returned %0h, expected 2100", result);
      $finish;
    end

    // Test const ref task in class
    adp.display(my_tx, "TX");

    $display("PASSED");
  end
endmodule
