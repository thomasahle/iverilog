// Test class object comparison to null
module test;
  class item;
    int value;
    function new(int v = 0);
      value = v;
    endfunction
  endclass

  item obj1;
  item obj2;

  initial begin
    // Test null comparisons
    if (obj1 != null) begin
      $display("FAILED: obj1 should be null initially");
      $finish;
    end

    obj1 = new(42);
    if (obj1 == null) begin
      $display("FAILED: obj1 should not be null after new");
      $finish;
    end

    // Test same reference
    obj2 = obj1;
    if (obj2 == null) begin
      $display("FAILED: obj2 should not be null after assignment");
      $finish;
    end

    // Test value access
    if (obj1.value != 42) begin
      $display("FAILED: obj1.value should be 42, got %0d", obj1.value);
      $finish;
    end
    
    if (obj2.value != 42) begin
      $display("FAILED: obj2.value should be 42, got %0d", obj2.value);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
