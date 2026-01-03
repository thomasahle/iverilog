// Test enum methods
module test;
  typedef enum {RED, GREEN, BLUE, YELLOW} color_e;
  color_e c;
  int errors = 0;

  initial begin
    // Test basic enum
    c = RED;
    if (c != RED) begin
      $display("FAILED: initial c = %s", c.name());
      errors++;
    end

    // Test name() method
    c = GREEN;
    if (c.name() != "GREEN") begin
      $display("FAILED: GREEN.name() = %s", c.name());
      errors++;
    end

    // Test next() method
    c = RED;
    c = c.next();
    if (c != GREEN) begin
      $display("FAILED: RED.next() = %s, expected GREEN", c.name());
      errors++;
    end

    // Test prev() method
    c = BLUE;
    c = c.prev();
    if (c != GREEN) begin
      $display("FAILED: BLUE.prev() = %s, expected GREEN", c.name());
      errors++;
    end

    // Test first() method
    c = c.first();
    if (c != RED) begin
      $display("FAILED: first() = %s, expected RED", c.name());
      errors++;
    end

    // Test last() method
    c = c.last();
    if (c != YELLOW) begin
      $display("FAILED: last() = %s, expected YELLOW", c.name());
      errors++;
    end

    // Test numeric value
    c = BLUE;
    if (c != 2) begin
      $display("FAILED: BLUE value = %0d, expected 2", c);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
