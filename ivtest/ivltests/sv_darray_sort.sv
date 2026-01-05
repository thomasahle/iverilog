// Test dynamic array sorting and manipulation methods: sort, rsort, reverse, shuffle
module test;
  int arr[];
  int passed = 0;
  int failed = 0;
  int i;

  function bit is_sorted_asc(int a[]);
    for (int i = 0; i < a.size() - 1; i++) begin
      if (a[i] > a[i+1]) return 0;
    end
    return 1;
  endfunction

  function bit is_sorted_desc(int a[]);
    for (int i = 0; i < a.size() - 1; i++) begin
      if (a[i] < a[i+1]) return 0;
    end
    return 1;
  endfunction

  function bit is_reversed(int a[], int original[]);
    if (a.size() != original.size()) return 0;
    for (int i = 0; i < a.size(); i++) begin
      if (a[i] != original[a.size()-1-i]) return 0;
    end
    return 1;
  endfunction

  initial begin
    // Initialize dynamic array
    arr = new[5];
    arr[0] = 3;
    arr[1] = 1;
    arr[2] = 4;
    arr[3] = 1;
    arr[4] = 5;

    // Test sort()
    arr.sort();
    if (is_sorted_asc(arr)) begin
      $display("PASSED: sort() - array is sorted ascending");
      passed++;
    end else begin
      $display("FAILED: sort() - array is not sorted");
      $display("  arr = %p", arr);
      failed++;
    end

    // Test rsort()
    arr[0] = 2;
    arr[1] = 7;
    arr[2] = 1;
    arr[3] = 8;
    arr[4] = 3;
    arr.rsort();
    if (is_sorted_desc(arr)) begin
      $display("PASSED: rsort() - array is sorted descending");
      passed++;
    end else begin
      $display("FAILED: rsort() - array is not sorted descending");
      $display("  arr = %p", arr);
      failed++;
    end

    // Test reverse()
    arr[0] = 10;
    arr[1] = 20;
    arr[2] = 30;
    arr[3] = 40;
    arr[4] = 50;
    arr.reverse();
    if (arr[0] == 50 && arr[1] == 40 && arr[2] == 30 && arr[3] == 20 && arr[4] == 10) begin
      $display("PASSED: reverse() - array is reversed");
      passed++;
    end else begin
      $display("FAILED: reverse() - array is not reversed correctly");
      $display("  arr = %p", arr);
      failed++;
    end

    // Test shuffle()
    arr[0] = 1;
    arr[1] = 2;
    arr[2] = 3;
    arr[3] = 4;
    arr[4] = 5;
    arr.shuffle();
    // Just verify that it doesn't crash and elements are still present
    // (since shuffle is random, we can't check the exact order)
    begin
      int sum = 0;
      for (i = 0; i < arr.size(); i++) begin
        sum += arr[i];
      end
      if (sum == 15 && arr.size() == 5) begin
        $display("PASSED: shuffle() - array was shuffled (sum preserved)");
        passed++;
      end else begin
        $display("FAILED: shuffle() - elements were lost");
        $display("  arr = %p", arr);
        failed++;
      end
    end

    // Test with negative numbers
    arr[0] = -5;
    arr[1] = 10;
    arr[2] = -3;
    arr[3] = 0;
    arr[4] = 7;
    arr.sort();
    if (arr[0] == -5 && arr[1] == -3 && arr[2] == 0 && arr[3] == 7 && arr[4] == 10) begin
      $display("PASSED: sort() with negative numbers");
      passed++;
    end else begin
      $display("FAILED: sort() with negative numbers");
      $display("  arr = %p", arr);
      failed++;
    end

    // Test rsort with negative numbers
    arr.rsort();
    if (arr[0] == 10 && arr[1] == 7 && arr[2] == 0 && arr[3] == -3 && arr[4] == -5) begin
      $display("PASSED: rsort() with negative numbers");
      passed++;
    end else begin
      $display("FAILED: rsort() with negative numbers");
      $display("  arr = %p", arr);
      failed++;
    end

    // Summary
    $display("\nTotal: %0d passed, %0d failed", passed, failed);
    if (failed == 0)
      $display("ALL TESTS PASSED");
    else
      $display("SOME TESTS FAILED");
  end
endmodule
