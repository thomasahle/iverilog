// Test foreach on dynamic int array class properties
// Tests various operations inside foreach body

class Statistics;
  int data[];

  function new(int size);
    data = new[size];
    for (int i = 0; i < size; i++)
      data[i] = i * 10;  // 0, 10, 20, 30, ...
  endfunction

  // Calculate sum using foreach
  function int sum();
    int total;
    total = 0;
    foreach (data[i]) begin
      total = total + data[i];
    end
    return total;
  endfunction

  // Find maximum using foreach
  function int max();
    int m;
    m = data[0];
    foreach (data[i]) begin
      if (data[i] > m)
        m = data[i];
    end
    return m;
  endfunction

  // Count elements matching condition
  function int count_gt(int threshold);
    int cnt;
    cnt = 0;
    foreach (data[i]) begin
      if (data[i] > threshold)
        cnt = cnt + 1;
    end
    return cnt;
  endfunction

  // Check if any element matches
  function bit contains(int val);
    foreach (data[i]) begin
      if (data[i] == val)
        return 1;
    end
    return 0;
  endfunction
endclass

module test;
  Statistics stats;
  int errors;

  initial begin
    errors = 0;

    // Create array with 5 elements: 0, 10, 20, 30, 40
    stats = new(5);

    // Test 1: Sum (0+10+20+30+40 = 100)
    if (stats.sum() !== 100) begin
      $display("FAILED: Test 1 - sum = %0d, expected 100", stats.sum());
      errors = errors + 1;
    end

    // Test 2: Max (40)
    if (stats.max() !== 40) begin
      $display("FAILED: Test 2 - max = %0d, expected 40", stats.max());
      errors = errors + 1;
    end

    // Test 3: Count > 15 (should be 3: 20, 30, 40)
    if (stats.count_gt(15) !== 3) begin
      $display("FAILED: Test 3 - count_gt(15) = %0d, expected 3", stats.count_gt(15));
      errors = errors + 1;
    end

    // Test 4: Contains 20 (yes)
    if (!stats.contains(20)) begin
      $display("FAILED: Test 4 - contains(20) should be true");
      errors = errors + 1;
    end

    // Test 5: Contains 25 (no)
    if (stats.contains(25)) begin
      $display("FAILED: Test 5 - contains(25) should be false");
      errors = errors + 1;
    end

    if (errors == 0)
      $display("PASSED");
  end
endmodule
