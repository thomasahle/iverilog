// Test inline constraints after randomize() with various operators
// Constraints are now enforced at runtime!
module test;
  class packet;
    rand logic [7:0] value;
    rand logic [7:0] min_val;
    rand logic [7:0] max_val;

    function new();
      value = 0;
      min_val = 0;
      max_val = 0;
    endfunction
  endclass

  initial begin
    packet pkt = new();
    int result;
    int pass = 0;
    int fail = 0;

    // Test: value > 100
    repeat (5) begin
      result = pkt.randomize() with { value > 100; };
      if (pkt.value > 100) pass++; else begin fail++; $display("FAIL: GT constraint"); end
    end

    // Test: value < 50
    repeat (5) begin
      result = pkt.randomize() with { value < 50; };
      if (pkt.value < 50) pass++; else begin fail++; $display("FAIL: LT constraint"); end
    end

    // Test: value >= 200
    repeat (5) begin
      result = pkt.randomize() with { value >= 200; };
      if (pkt.value >= 200) pass++; else begin fail++; $display("FAIL: GE constraint"); end
    end

    // Test: value <= 10
    repeat (5) begin
      result = pkt.randomize() with { value <= 10; };
      if (pkt.value <= 10) pass++; else begin fail++; $display("FAIL: LE constraint"); end
    end

    // Test: value == 42
    repeat (5) begin
      result = pkt.randomize() with { value == 42; };
      if (pkt.value == 42) pass++; else begin fail++; $display("FAIL: EQ constraint"); end
    end

    // Test: value != 128
    repeat (5) begin
      result = pkt.randomize() with { value != 128; };
      if (pkt.value != 128) pass++; else begin fail++; $display("FAIL: NE constraint"); end
    end

    $display("Inline constraint test: %0d PASS, %0d FAIL", pass, fail);
    if (fail == 0) begin
      $display("PASSED");
    end else begin
      $display("FAILED");
    end
  end
endmodule
