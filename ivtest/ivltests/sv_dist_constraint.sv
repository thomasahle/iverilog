// Test dist constraint in randomize() with {...}
// The dist constraint specifies allowed discrete values
// Currently weights are parsed but not enforced (uniform distribution)

class DistTest;
  rand bit [3:0] value;
  rand bit [7:0] data;

  function new();
    value = 0;
    data = 0;
  endfunction
endclass

module test;
  DistTest obj;
  int count_value[16];
  int count_data[256];
  int i;

  initial begin
    obj = new();

    // Test 1: dist with discrete values
    $display("Test 1: value dist {1, 3, 5}");
    for (i = 0; i < 16; i++) count_value[i] = 0;

    for (i = 0; i < 100; i++) begin
      if (obj.randomize() with { value dist {1:=1, 3:=1, 5:=1}; }) begin
        count_value[obj.value]++;
      end
    end

    // Check only 1, 3, 5 were generated
    if (count_value[0] == 0 && count_value[2] == 0 && count_value[4] == 0 &&
        count_value[6] == 0 && count_value[7] == 0 && count_value[8] == 0 &&
        count_value[1] > 0 && count_value[3] > 0 && count_value[5] > 0) begin
      $display("  PASSED: Only values 1, 3, 5 were generated");
    end else begin
      $display("  FAILED: Unexpected values generated");
      for (i = 0; i < 16; i++) begin
        if (count_value[i] > 0) $display("    value=%0d: count=%0d", i, count_value[i]);
      end
    end

    // Test 2: dist with range
    $display("Test 2: data dist {[10:20]}");
    for (i = 0; i < 256; i++) count_data[i] = 0;

    for (i = 0; i < 100; i++) begin
      if (obj.randomize() with { data dist {[10:20]:=1}; }) begin
        count_data[obj.data]++;
      end
    end

    // Check all values are in range [10:20]
    begin
      int out_of_range = 0;
      int in_range = 0;
      for (i = 0; i < 256; i++) begin
        if (count_data[i] > 0) begin
          if (i >= 10 && i <= 20) in_range++;
          else out_of_range++;
        end
      end
      if (out_of_range == 0 && in_range > 0) begin
        $display("  PASSED: All values in [10:20] range");
      end else begin
        $display("  FAILED: %0d out of range, %0d in range", out_of_range, in_range);
      end
    end

    // Test 3: dist with more discrete values
    $display("Test 3: value dist {0, 5, 10, 15}");
    for (i = 0; i < 16; i++) count_value[i] = 0;

    for (i = 0; i < 100; i++) begin
      if (obj.randomize() with { value dist {0:=1, 5:=1, 10:=1, 15:=1}; }) begin
        count_value[obj.value]++;
      end
    end

    // Check only 0, 5, 10, 15 were generated
    begin
      int unexpected = 0;
      int expected = 0;
      for (i = 0; i < 16; i++) begin
        if (count_value[i] > 0) begin
          if (i == 0 || i == 5 || i == 10 || i == 15) expected++;
          else unexpected++;
        end
      end
      if (unexpected == 0 && expected > 0) begin
        $display("  PASSED: Only values 0, 5, 10, 15 were generated");
      end else begin
        $display("  FAILED: %0d unexpected values", unexpected);
        for (i = 0; i < 16; i++) begin
          if (count_value[i] > 0) $display("    value=%0d: count=%0d", i, count_value[i]);
        end
      end
    end

    $display("All dist constraint tests completed");
  end
endmodule
