// Test null class references
class item;
  int value;
  function new(int v);
    value = v;
  endfunction
endclass

module test;
  item it;
  item arr[$];
  int errors = 0;

  initial begin
    // Test initial null
    if (it != null) begin
      $display("FAILED: uninitialized item is not null");
      errors++;
    end

    // Test explicit null assignment
    it = null;
    if (it != null) begin
      $display("FAILED: explicit null assignment failed");
      errors++;
    end

    // Test non-null after construction
    it = new(42);
    if (it == null) begin
      $display("FAILED: constructed item is null");
      errors++;
    end
    if (it.value != 42) begin
      $display("FAILED: it.value = %0d, expected 42", it.value);
      errors++;
    end

    // Test setting back to null
    it = null;
    if (it != null) begin
      $display("FAILED: reset to null failed");
      errors++;
    end

    // Test queue with items
    it = new(10);
    arr.push_back(it);
    it = new(20);
    arr.push_back(it);
    if (arr.size() != 2) begin
      $display("FAILED: queue size = %0d, expected 2", arr.size());
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
