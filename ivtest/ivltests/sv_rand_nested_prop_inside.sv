// Test for randomize with inside constraint using nested property chain
// Tests both sign-extended values (>= 0x80) and normal values

class InnerConfig;
  bit [7:0] targetAddress;
endclass

class OuterConfig;
  InnerConfig inner;

  function new();
    inner = new();
  endfunction
endclass

class Transaction;
  rand bit [7:0] addr;
  OuterConfig cfg;

  function new();
    cfg = new();
  endfunction
endclass

module test;
  Transaction tx;
  int passed = 0;
  int failed = 0;

  // Test helper task
  task test_value(input bit [7:0] test_val);
    tx.cfg.inner.targetAddress = test_val;
    if (!tx.randomize() with { addr inside {tx.cfg.inner.targetAddress}; }) begin
      $display("FAILED: Value %h - randomization failed", test_val);
      failed++;
    end else if (tx.addr != test_val) begin
      $display("FAILED: Value %h - addr=%h doesn't match", test_val, tx.addr);
      failed++;
    end else begin
      passed++;
    end
  endtask

  initial begin
    tx = new();

    // Test values below sign extension boundary
    test_value(8'h00);
    test_value(8'h05);
    test_value(8'h7F);

    // Test values at and above sign extension boundary
    test_value(8'h80);
    test_value(8'hAB);
    test_value(8'hFF);

    if (failed == 0)
      $display("PASSED: All %0d tests passed", passed);
    else
      $display("FAILED: %0d passed, %0d failed", passed, failed);
    $finish;
  end
endmodule
