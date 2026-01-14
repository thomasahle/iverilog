// Test enum methods when declaration order differs from lexicographic order
// This verifies that first(), last(), next(), prev() use declaration order,
// not the lexicographic order of std::map.
//
// Declaration order: ZZZ, AAA, MMM
// Lexicographic order: AAA, MMM, ZZZ

module test;

  typedef enum bit [1:0] {
    ZZZ = 2'b00,  // First declared, but LAST lexicographically
    AAA = 2'b01,  // Second declared, but FIRST lexicographically
    MMM = 2'b10   // Third declared, MIDDLE lexicographically
  } state_t;

  initial begin
    state_t s;
    int pass_count = 0;
    int fail_count = 0;

    // Test first() - should return ZZZ (first declared)
    s = AAA;
    s = s.first();
    if (s == ZZZ) begin
      $display("PASS: first() = %s (expected ZZZ)", s.name());
      pass_count++;
    end else begin
      $display("FAIL: first() = %s, expected ZZZ", s.name());
      fail_count++;
    end

    // Test last() - should return MMM (last declared)
    s = AAA;
    s = s.last();
    if (s == MMM) begin
      $display("PASS: last() = %s (expected MMM)", s.name());
      pass_count++;
    end else begin
      $display("FAIL: last() = %s, expected MMM", s.name());
      fail_count++;
    end

    // Test next() from ZZZ - should return AAA (second declared)
    s = ZZZ;
    s = s.next();
    if (s == AAA) begin
      $display("PASS: ZZZ.next() = %s (expected AAA)", s.name());
      pass_count++;
    end else begin
      $display("FAIL: ZZZ.next() = %s, expected AAA", s.name());
      fail_count++;
    end

    // Test next() from AAA - should return MMM (third declared)
    s = AAA;
    s = s.next();
    if (s == MMM) begin
      $display("PASS: AAA.next() = %s (expected MMM)", s.name());
      pass_count++;
    end else begin
      $display("FAIL: AAA.next() = %s, expected MMM", s.name());
      fail_count++;
    end

    // Test next() wrapping from MMM - should return ZZZ (first declared)
    s = MMM;
    s = s.next();
    if (s == ZZZ) begin
      $display("PASS: MMM.next() = %s (expected ZZZ, wrap)", s.name());
      pass_count++;
    end else begin
      $display("FAIL: MMM.next() = %s, expected ZZZ (wrap)", s.name());
      fail_count++;
    end

    // Test prev() from AAA - should return ZZZ (first declared)
    s = AAA;
    s = s.prev();
    if (s == ZZZ) begin
      $display("PASS: AAA.prev() = %s (expected ZZZ)", s.name());
      pass_count++;
    end else begin
      $display("FAIL: AAA.prev() = %s, expected ZZZ", s.name());
      fail_count++;
    end

    // Test prev() wrapping from ZZZ - should return MMM (last declared)
    s = ZZZ;
    s = s.prev();
    if (s == MMM) begin
      $display("PASS: ZZZ.prev() = %s (expected MMM, wrap)", s.name());
      pass_count++;
    end else begin
      $display("FAIL: ZZZ.prev() = %s, expected MMM (wrap)", s.name());
      fail_count++;
    end

    // Iterate through all values in declaration order
    $display("Iterating through all values:");
    s = s.first();
    repeat (s.num()) begin
      $display("  %s = %0d", s.name(), s);
      s = s.next();
    end

    $display("Pass: %0d, Fail: %0d", pass_count, fail_count);
    if (fail_count == 0)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end

endmodule
