// Test indexed array constraint on dynamic arrays
// data[0] == 42 should set element 0 to 42, not all elements

class Transaction;
  rand bit [7:0] data[];

  function new();
    data = new[4];
  endfunction
endclass

module test;
  Transaction t;
  int passed;

  initial begin
    passed = 1;
    t = new();

    // Test 1: Single indexed constraint
    if (!t.randomize() with { data.size() == 4; data[0] == 42; }) begin
      $display("FAIL: Test 1 - randomize failed");
      passed = 0;
    end else begin
      if (t.data[0] != 42) begin
        $display("FAIL: Test 1 - data[0]=%0d (should be 42)", t.data[0]);
        passed = 0;
      end
      // Other elements should be randomized (not necessarily 42)
    end

    // Test 2: Multiple indexed constraints
    if (!t.randomize() with { data.size() == 4; data[0] == 10; data[1] == 20; data[3] == 40; }) begin
      $display("FAIL: Test 2 - randomize failed");
      passed = 0;
    end else begin
      if (t.data[0] != 10) begin
        $display("FAIL: Test 2 - data[0]=%0d (should be 10)", t.data[0]);
        passed = 0;
      end
      if (t.data[1] != 20) begin
        $display("FAIL: Test 2 - data[1]=%0d (should be 20)", t.data[1]);
        passed = 0;
      end
      if (t.data[3] != 40) begin
        $display("FAIL: Test 2 - data[3]=%0d (should be 40)", t.data[3]);
        passed = 0;
      end
    end

    // Test 3: Indexed constraint with bounds
    if (!t.randomize() with { data.size() == 4; data[0] >= 100; data[0] <= 110; }) begin
      $display("FAIL: Test 3 - randomize failed");
      passed = 0;
    end else begin
      if (t.data[0] < 100 || t.data[0] > 110) begin
        $display("FAIL: Test 3 - data[0]=%0d (should be 100-110)", t.data[0]);
        passed = 0;
      end
    end

    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
