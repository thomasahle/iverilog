// Test dist constraint with unbounded ranges [low:$] and [$:high]

class UnboundedDistTest;
  rand bit [7:0] value;

  function new();
    value = 0;
  endfunction
endclass

module test;
  UnboundedDistTest obj;
  int low_count, mid_count, high_count;
  int i;

  initial begin
    obj = new();

    // Test 1: [100:$] - should generate values >= 100
    $display("Test 1: value dist {[100:$]:=1}");
    low_count = 0;
    high_count = 0;

    for (i = 0; i < 100; i++) begin
      if (obj.randomize() with { value dist {[100:$]:=1}; }) begin
        if (obj.value >= 100) high_count++;
        else low_count++;
      end
    end

    if (low_count == 0 && high_count == 100) begin
      $display("  PASSED: All values >= 100");
    end else begin
      $display("  FAILED: %0d values < 100, %0d values >= 100", low_count, high_count);
    end

    // Test 2: [$:50] - should generate values <= 50
    $display("Test 2: value dist {[$:50]:=1}");
    low_count = 0;
    high_count = 0;

    for (i = 0; i < 100; i++) begin
      if (obj.randomize() with { value dist {[$:50]:=1}; }) begin
        if (obj.value <= 50) low_count++;
        else high_count++;
      end
    end

    if (high_count == 0 && low_count == 100) begin
      $display("  PASSED: All values <= 50");
    end else begin
      $display("  FAILED: %0d values <= 50, %0d values > 50", low_count, high_count);
    end

    // Test 3: Mix of bounded and unbounded
    $display("Test 3: value dist {[0:10]:=1, [200:$]:=1}");
    low_count = 0;    // 0-10
    mid_count = 0;    // 11-199 (should be 0)
    high_count = 0;   // 200+

    for (i = 0; i < 100; i++) begin
      if (obj.randomize() with { value dist {[0:10]:=1, [200:$]:=1}; }) begin
        if (obj.value <= 10) low_count++;
        else if (obj.value >= 200) high_count++;
        else mid_count++;
      end
    end

    if (mid_count == 0 && (low_count + high_count) == 100) begin
      $display("  PASSED: All values in [0:10] or [200:255]");
    end else begin
      $display("  FAILED: %0d in [0:10], %0d in [200:255], %0d in between", low_count, high_count, mid_count);
    end

    $display("All unbounded dist tests completed");
  end
endmodule
