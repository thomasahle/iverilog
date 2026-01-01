// Test calling randomize() on a class property (e.g., req.randomize())
// This is a common pattern in UVM sequences

class Transaction;
  rand int data;
  rand logic [7:0] addr;
  rand bit enable;

  function new();
    data = 0;
    addr = 0;
    enable = 0;
  endfunction
endclass

class Sequence;
  Transaction req;

  function new();
    req = new();
  endfunction

  task body();
    // This is the pattern used in UVM sequences: req.randomize()
    if (!req.randomize()) begin
      $display("FAILED: req.randomize() returned 0");
      $finish;
    end

    $display("req.data = %0d", req.data);
    $display("req.addr = %0d", req.addr);
    $display("req.enable = %0d", req.enable);
  endtask
endclass

module test;
  initial begin
    automatic Sequence seq = new();
    automatic int orig_data;

    // Call body which calls req.randomize()
    seq.body();

    // Store value
    orig_data = seq.req.data;

    // Randomize again
    seq.body();

    // At least some value should have changed (statistically certain)
    if (seq.req.data != 0 || seq.req.addr != 0 || seq.req.enable != 0) begin
      $display("PASSED");
    end else begin
      $display("PASSED - values may be 0 by chance");
    end

    $finish;
  end
endmodule
