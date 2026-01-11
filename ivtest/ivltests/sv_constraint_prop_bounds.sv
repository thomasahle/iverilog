// Test property-to-property bounds in constraints
//
// Demonstrates:
// - Single property with >= and <= to non-rand property WORKS
// - Multiple properties with >= only WORKS
// - Mix: one property with both bounds, others with >= WORKS
//
// LIMITATION: Multiple properties EACH with both >= and <= bounds
// to different non-rand properties causes randomize() to return 0.

class SingleBound;
  rand bit [7:0] value;
  bit [7:0] target;

  constraint c { value >= target; value <= target; }
endclass

class MultipleLower;
  rand bit [7:0] addr;
  rand bit [7:0] data;
  bit [7:0] min_addr;
  bit [7:0] min_data;

  constraint c { addr >= min_addr; data >= min_data; }
endclass

class MixedBounds;
  rand bit [7:0] addr;
  rand bit [7:0] data;
  bit [7:0] target_addr;
  bit [7:0] min_data;

  // addr pinned, data has lower bound only
  constraint c {
    addr >= target_addr;
    addr <= target_addr;
    data >= min_data;
  }
endclass

module test;
  initial begin
    SingleBound sb;
    MultipleLower ml;
    MixedBounds mb;
    int pass = 1;

    // Test 1: Single property bounds
    sb = new();
    sb.target = 8'h42;
    if (sb.randomize()) begin
      if (sb.value != 8'h42) begin
        $display("FAIL: single bound value %h != 42", sb.value);
        pass = 0;
      end
    end else begin
      $display("FAIL: single bound randomize returned 0");
      pass = 0;
    end

    // Test 2: Multiple lower bounds
    ml = new();
    ml.min_addr = 8'h10;
    ml.min_data = 8'h20;
    if (ml.randomize()) begin
      if (ml.addr < 8'h10 || ml.data < 8'h20) begin
        $display("FAIL: lower bounds not honored");
        pass = 0;
      end
    end else begin
      $display("FAIL: multiple lower randomize returned 0");
      pass = 0;
    end

    // Test 3: Mixed bounds
    mb = new();
    mb.target_addr = 8'h55;
    mb.min_data = 8'h30;
    if (mb.randomize()) begin
      if (mb.addr != 8'h55 || mb.data < 8'h30) begin
        $display("FAIL: mixed bounds not honored (addr=%h, data=%h)",
                 mb.addr, mb.data);
        pass = 0;
      end
    end else begin
      $display("FAIL: mixed bounds randomize returned 0");
      pass = 0;
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
