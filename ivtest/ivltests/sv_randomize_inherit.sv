// Test randomize() with class inheritance

class base_transaction;
  rand int base_data;

  function new();
    base_data = 0;
  endfunction
endclass

class derived_transaction extends base_transaction;
  rand int derived_data;
  rand logic [15:0] extra;

  function new();
    super.new();
    derived_data = 0;
    extra = 0;
  endfunction
endclass

module test;
  initial begin
    automatic derived_transaction tx;
    automatic base_transaction base_handle;
    automatic int passed = 1;

    tx = new();

    // Call randomize on derived class
    if (!tx.randomize()) begin
      $display("FAILED: tx.randomize() returned 0");
      passed = 0;
    end else begin
      $display("Derived randomize succeeded:");
      $display("  base_data=%0d", tx.base_data);
      $display("  derived_data=%0d", tx.derived_data);
      $display("  extra=%0d", tx.extra);
    end

    // Assign to base class handle and randomize
    base_handle = tx;
    if (!base_handle.randomize()) begin
      $display("FAILED: base_handle.randomize() returned 0");
      passed = 0;
    end else begin
      $display("Base handle randomize succeeded:");
      $display("  base_data=%0d", base_handle.base_data);
    end

    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
