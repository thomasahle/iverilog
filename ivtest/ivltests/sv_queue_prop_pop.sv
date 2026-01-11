// Test pop_front() and pop_back() on queue class properties
// Tests whether queue methods work on queues that are class properties

module test;

  class Container;
    bit [7:0] data[$];

    function void add(bit [7:0] val);
      data.push_back(val);
    endfunction

    // Use methods to wrap queue operations
    function bit [7:0] remove_first();
      return data.pop_front();
    endfunction

    function bit [7:0] remove_last();
      return data.pop_back();
    endfunction

    function int get_size();
      return data.size();
    endfunction
  endclass

  initial begin
    Container c;
    bit [7:0] val;

    c = new();

    // Add elements
    c.add(8'h10);
    c.add(8'h20);
    c.add(8'h30);

    $display("Size after adds: %0d", c.get_size());
    if (c.get_size() != 3) begin
      $display("FAILED: Expected size 3");
      $finish;
    end

    // Test pop_front via wrapper method
    val = c.remove_first();
    $display("remove_first() returned: 0x%h (expected 0x10)", val);
    if (val != 8'h10) begin
      $display("FAILED: Expected 0x10");
      $finish;
    end

    // Test pop_back via wrapper method
    val = c.remove_last();
    $display("remove_last() returned: 0x%h (expected 0x30)", val);
    if (val != 8'h30) begin
      $display("FAILED: Expected 0x30");
      $finish;
    end

    $display("Size after pops: %0d (expected 1)", c.get_size());
    if (c.get_size() != 1) begin
      $display("FAILED: Expected size 1");
      $finish;
    end

    // Verify remaining element via direct access
    if (c.data[0] != 8'h20) begin
      $display("FAILED: Expected remaining element 0x20");
      $finish;
    end

    $display("Queue class property operations working via wrapper methods");
    $display("PASSED");
    $finish;
  end

endmodule
