// Test foreach loop on arrays
// This test verifies that foreach correctly iterates over arrays.

module test;
  // Unpacked array
  logic [7:0] arr [4];
  int sum;

  initial begin
    sum = 0;

    // Initialize array
    arr[0] = 10;
    arr[1] = 20;
    arr[2] = 30;
    arr[3] = 40;

    // foreach on unpacked array
    foreach(arr[i]) begin
      sum = sum + arr[i];
    end

    // Verify: 10 + 20 + 30 + 40 = 100
    if (sum == 100) begin
      $display("PASSED");
    end else begin
      $display("FAILED: sum=%0d, expected 100", sum);
    end
    $finish;
  end
endmodule
