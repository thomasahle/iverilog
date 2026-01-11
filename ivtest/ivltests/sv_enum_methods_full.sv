// Test all enum methods
// Verifies: name(), first(), last(), next(), prev(), num()

module test;

  typedef enum bit [2:0] {
    IDLE  = 3'b000,
    READ  = 3'b001,
    WRITE = 3'b010,
    BURST = 3'b011,
    ERROR = 3'b100
  } state_t;

  initial begin
    state_t s;
    string name_str;

    // Test name()
    s = READ;
    name_str = s.name();
    if (name_str != "READ") begin
      $display("FAILED: name() = '%s', expected 'READ'", name_str);
      $finish;
    end
    $display("name() test: %s = %s", s.name(), name_str);

    // Test first()
    s = s.first();
    if (s != IDLE) begin
      $display("FAILED: first() = %s, expected IDLE", s.name());
      $finish;
    end
    $display("first() test: %s", s.name());

    // Test last()
    s = s.last();
    if (s != ERROR) begin
      $display("FAILED: last() = %s, expected ERROR", s.name());
      $finish;
    end
    $display("last() test: %s", s.name());

    // Test next()
    s = IDLE;
    s = s.next();
    if (s != READ) begin
      $display("FAILED: next() from IDLE = %s, expected READ", s.name());
      $finish;
    end
    $display("next() test: IDLE.next() = %s", s.name());

    // Test next() wrapping
    s = ERROR;
    s = s.next();
    if (s != IDLE) begin
      $display("FAILED: next() from ERROR = %s, expected IDLE (wrap)", s.name());
      $finish;
    end
    $display("next() wrap test: ERROR.next() = %s", s.name());

    // Test prev()
    s = READ;
    s = s.prev();
    if (s != IDLE) begin
      $display("FAILED: prev() from READ = %s, expected IDLE", s.name());
      $finish;
    end
    $display("prev() test: READ.prev() = %s", s.name());

    // Test prev() wrapping
    s = IDLE;
    s = s.prev();
    if (s != ERROR) begin
      $display("FAILED: prev() from IDLE = %s, expected ERROR (wrap)", s.name());
      $finish;
    end
    $display("prev() wrap test: IDLE.prev() = %s", s.name());

    // Test num()
    if (s.num() != 5) begin
      $display("FAILED: num() = %0d, expected 5", s.num());
      $finish;
    end
    $display("num() test: %0d enum values", s.num());

    // Iterate through all values
    $display("Iterating through all values:");
    s = s.first();
    repeat (s.num()) begin
      $display("  %s = %0d", s.name(), s);
      s = s.next();
    end

    $display("All enum methods working correctly");
    $display("PASSED");
    $finish;
  end

endmodule
