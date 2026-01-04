// Test weighted distribution syntax in dist constraints
// Note: Parser accepts := and :/ weights but they are not yet enforced
// (uniform distribution is used)
module test;
  class MyClass;
    rand int value;
  endclass

  MyClass obj;
  int count1, count5;

  initial begin
    obj = new();

    // Test := syntax (equal weight per value)
    count1 = 0;
    count5 = 0;
    for (int i = 0; i < 100; i++) begin
      if (obj.randomize() with { value dist { 1 := 10, 5 := 90 }; }) begin
        if (obj.value == 1) count1++;
        else if (obj.value == 5) count5++;
      end else begin
        $display("FAILED: randomize returned 0");
        $finish;
      end
    end

    $display("Test 1: := syntax (equal weight per value)");
    $display("  1 appeared: %0d times", count1);
    $display("  5 appeared: %0d times", count5);

    // Verify values are from the allowed set
    if (count1 + count5 != 100) begin
      $display("FAILED: values not from allowed set");
      $finish;
    end

    // Test :/ syntax (weight divided across range)
    count1 = 0;  // use for [1:5] range
    count5 = 0;  // use for [6:10] range
    for (int i = 0; i < 100; i++) begin
      if (obj.randomize() with { value dist { [1:5] :/ 10, [6:10] :/ 90 }; }) begin
        if (obj.value >= 1 && obj.value <= 5) count1++;
        else if (obj.value >= 6 && obj.value <= 10) count5++;
        else begin
          $display("FAILED: value %0d outside allowed ranges", obj.value);
          $finish;
        end
      end else begin
        $display("FAILED: randomize returned 0");
        $finish;
      end
    end

    $display("Test 2: :/ syntax (weight divided across range)");
    $display("  [1:5] appeared: %0d times", count1);
    $display("  [6:10] appeared: %0d times", count5);

    // Verify all values are within ranges
    if (count1 + count5 != 100) begin
      $display("FAILED: values not from allowed ranges");
      $finish;
    end

    $display("PASSED");
  end
endmodule
