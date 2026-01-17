// Test for array/structure replication '{n{pattern}}
// IEEE 1800-2017 Section 10.9.1

module test;
  int arr[4];
  int arr2[3];
  int arr3[6];
  int arr4[4];
  int nested[1:2][1:6];

  bit passed = 1;

  initial begin
    // Test basic single-item replication
    arr = '{4{1}};
    if (arr[0] !== 1 || arr[1] !== 1 || arr[2] !== 1 || arr[3] !== 1) begin
      $display("FAILED: '{4{1}} - got %0d %0d %0d %0d", arr[0], arr[1], arr[2], arr[3]);
      passed = 0;
    end

    // Test with different value
    arr2 = '{3{42}};
    if (arr2[0] !== 42 || arr2[1] !== 42 || arr2[2] !== 42) begin
      $display("FAILED: '{3{42}} - got %0d %0d %0d", arr2[0], arr2[1], arr2[2]);
      passed = 0;
    end

    // Test with multiple items
    arr3 = '{3{1, 2}};  // Should be {1,2,1,2,1,2}
    if (arr3[0] !== 1 || arr3[1] !== 2 || arr3[2] !== 1 ||
        arr3[3] !== 2 || arr3[4] !== 1 || arr3[5] !== 2) begin
      $display("FAILED: '{3{1, 2}} - got %0d %0d %0d %0d %0d %0d",
               arr3[0], arr3[1], arr3[2], arr3[3], arr3[4], arr3[5]);
      passed = 0;
    end

    // Test with expression as count
    arr4 = '{2*2{100}};
    if (arr4[0] !== 100 || arr4[1] !== 100 || arr4[2] !== 100 || arr4[3] !== 100) begin
      $display("FAILED: '{2*2{100}} - got %0d %0d %0d %0d", arr4[0], arr4[1], arr4[2], arr4[3]);
      passed = 0;
    end

    // Test nested replication
    nested = '{2{'{3{4, 5}}}};  // 2x6 array filled with alternating 4,5
    if (nested[1][1] !== 4 || nested[1][2] !== 5 || nested[1][3] !== 4 ||
        nested[1][4] !== 5 || nested[1][5] !== 4 || nested[1][6] !== 5 ||
        nested[2][1] !== 4 || nested[2][2] !== 5 || nested[2][3] !== 4 ||
        nested[2][4] !== 5 || nested[2][5] !== 4 || nested[2][6] !== 5) begin
      $display("FAILED: nested replication");
      passed = 0;
    end

    if (passed)
      $display("PASSED");
    $finish;
  end
endmodule
