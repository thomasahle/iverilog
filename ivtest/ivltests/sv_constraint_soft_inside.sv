// Test soft inside constraint with constant bounds
// Verifies: soft constraint with inside range
// Note: Module parameters not visible in class constraints - use constants

module test;

  class Transaction;
    rand bit [31:0] addr;
    rand bit [7:0] data;

    // Use constants instead of parameters (parameters not visible in class scope)
    constraint addr_c { soft addr inside {[32'h100:32'h1FF]}; }
  endclass

  initial begin
    Transaction tx;
    int i;
    int in_range;

    tx = new();
    in_range = 0;

    // Test soft inside with constant bounds
    for (i = 0; i < 20; i++) begin
      if (!tx.randomize()) begin
        $display("FAILED: randomize failed");
        $finish;
      end

      if (tx.addr >= 32'h100 && tx.addr <= 32'h1FF) begin
        in_range++;
      end
    end

    $display("In range: %0d/20", in_range);

    // All should be in range since soft constraint is active
    if (in_range != 20) begin
      $display("FAILED: Values outside range found (%0d != 20)", in_range);
      $finish;
    end

    // Test override with inline constraint
    if (!tx.randomize() with { addr == 32'h50; }) begin
      $display("FAILED: inline override randomize failed");
      $finish;
    end

    if (tx.addr != 32'h50) begin
      $display("FAILED: inline override didn't work, got %h", tx.addr);
      $finish;
    end

    $display("Soft inside constraint working");
    $display("PASSED");
    $finish;
  end

endmodule
