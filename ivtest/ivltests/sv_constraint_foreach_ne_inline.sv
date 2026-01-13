// Test inline foreach constraint with != on dynamic arrays
// This verifies that foreach(arr[i]) arr[i] != 0 works in randomize() with {...}

module test;
  class Transaction;
    rand int data[];

    function new();
      data = new[4];
    endfunction
  endclass

  initial begin
    Transaction t;
    int i, fail;

    t = new();
    fail = 0;

    // Test 20 randomizations with inline foreach != constraint
    for (i = 0; i < 20; i++) begin
      if (!t.randomize() with {
        data.size() == 4;
        foreach(data[j]) data[j] != 0;  // No element should be 0
      }) begin
        $display("FAILED: randomize() returned 0");
        $finish;
      end

      // Check constraint - no element should be 0
      for (int j = 0; j < 4; j++) begin
        if (t.data[j] == 0) begin
          $display("FAILED: data[%0d]=%0d (should not be 0)", j, t.data[j]);
          fail = 1;
        end
      end
    end

    if (fail)
      $display("FAILED");
    else
      $display("PASSED");
    $finish;
  end
endmodule
