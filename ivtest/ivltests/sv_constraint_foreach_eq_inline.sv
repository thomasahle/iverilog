// Test inline foreach constraint with == on dynamic arrays
// This verifies that foreach(arr[i]) arr[i] == value works in randomize() with {...}

module test;
  class Transaction;
    rand int data[];

    function new();
      data = new[4];
    endfunction
  endclass

  initial begin
    Transaction t;
    int i;

    t = new();

    // Test 1: All elements should be 42
    if (!t.randomize() with {
      data.size() == 4;
      foreach(data[j]) data[j] == 42;  // All elements should be 42
    }) begin
      $display("FAILED: randomize() returned 0");
      $finish;
    end

    // Check constraint - all elements should be 42
    for (int j = 0; j < 4; j++) begin
      if (t.data[j] != 42) begin
        $display("FAILED: Test1 data[%0d]=%0d (should be 42)", j, t.data[j]);
        $finish;
      end
    end

    // Test 2: All elements should be 100
    if (!t.randomize() with {
      data.size() == 3;
      foreach(data[j]) data[j] == 100;
    }) begin
      $display("FAILED: randomize() returned 0 for test 2");
      $finish;
    end

    // Check constraint - all elements should be 100
    for (int j = 0; j < 3; j++) begin
      if (t.data[j] != 100) begin
        $display("FAILED: Test2 data[%0d]=%0d (should be 100)", j, t.data[j]);
        $finish;
      end
    end

    // Test 3: All elements should be 0
    if (!t.randomize() with {
      data.size() == 5;
      foreach(data[j]) data[j] == 0;
    }) begin
      $display("FAILED: randomize() returned 0 for test 3");
      $finish;
    end

    for (int j = 0; j < 5; j++) begin
      if (t.data[j] != 0) begin
        $display("FAILED: Test3 data[%0d]=%0d (should be 0)", j, t.data[j]);
        $finish;
      end
    end

    $display("PASSED");
    $finish;
  end
endmodule
