// Test direct queue method calls on class properties
// Verifies: c.queue.push_back(), c.queue.pop_front(), etc.

module test;

  class Container;
    bit [7:0] data[$];
  endclass

  initial begin
    Container c;
    bit [7:0] val;

    c = new();

    // Direct push_back on queue property
    c.data.push_back(8'h10);
    c.data.push_back(8'h20);
    c.data.push_back(8'h30);

    $display("Size after push_back: %0d", c.data.size());
    if (c.data.size() != 3) begin
      $display("FAILED: Expected size 3, got %0d", c.data.size());
      $finish;
    end

    // Direct pop_front on queue property
    val = c.data.pop_front();
    $display("pop_front() returned: 0x%h (expected 0x10)", val);
    if (val != 8'h10) begin
      $display("FAILED: Expected 0x10");
      $finish;
    end

    // Direct pop_back on queue property
    val = c.data.pop_back();
    $display("pop_back() returned: 0x%h (expected 0x30)", val);
    if (val != 8'h30) begin
      $display("FAILED: Expected 0x30");
      $finish;
    end

    $display("Size after pops: %0d (expected 1)", c.data.size());
    if (c.data.size() != 1) begin
      $display("FAILED: Expected size 1");
      $finish;
    end

    // Direct element access
    val = c.data[0];
    if (val != 8'h20) begin
      $display("FAILED: Expected 0x20");
      $finish;
    end

    // Direct push_front
    c.data.push_front(8'h05);
    if (c.data[0] != 8'h05) begin
      $display("FAILED: push_front failed");
      $finish;
    end

    $display("All direct queue property operations working");
    $display("PASSED");
    $finish;
  end

endmodule
