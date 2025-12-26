// Test basic randomize() method on class properties

class my_transaction;
  rand int data;
  rand logic [7:0] addr;
  rand bit [3:0] id;

  // Non-random property
  int count;

  function new();
    data = 0;
    addr = 0;
    id = 0;
    count = 0;
  endfunction
endclass

module test;
  initial begin
    automatic my_transaction tx;
    automatic int passed = 1;
    automatic int orig_data, orig_addr, orig_id;

    tx = new();

    // Store original values
    orig_data = tx.data;
    orig_addr = tx.addr;
    orig_id = tx.id;

    // Call randomize
    if (!tx.randomize()) begin
      $display("FAILED: randomize() returned 0");
      passed = 0;
    end else begin
      $display("randomize succeeded:");
      $display("  data=%0d (was %0d)", tx.data, orig_data);
      $display("  addr=%0d (was %0d)", tx.addr, orig_addr);
      $display("  id=%0d (was %0d)", tx.id, orig_id);
    end

    // Randomize again and check values changed (statistically likely)
    orig_data = tx.data;
    if (!tx.randomize()) begin
      $display("FAILED: second randomize() returned 0");
      passed = 0;
    end

    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
