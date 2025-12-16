// Test: class variable declarations at module scope
// This tests that class instances can be declared at module level,
// not just inside initial/always blocks or functions.

class SimpleClass;
  int value;
  function new(int v = 0);
    value = v;
  endfunction
endclass

module test;
  // Class variable at module scope (not inside initial block)
  SimpleClass obj1;
  SimpleClass obj2 = new(100);  // With initialization
  SimpleClass obj3, obj4;       // Multiple declarations

  initial begin
    // Initialize obj1 and obj3/obj4 inside initial block
    obj1 = new(10);
    obj3 = new(30);
    obj4 = new(40);

    // Check all values
    if (obj1.value !== 10) begin
      $display("FAILED: obj1.value=%0d, expected 10", obj1.value);
      $finish;
    end
    if (obj2.value !== 100) begin
      $display("FAILED: obj2.value=%0d, expected 100", obj2.value);
      $finish;
    end
    if (obj3.value !== 30) begin
      $display("FAILED: obj3.value=%0d, expected 30", obj3.value);
      $finish;
    end
    if (obj4.value !== 40) begin
      $display("FAILED: obj4.value=%0d, expected 40", obj4.value);
      $finish;
    end
    $display("PASSED");
  end
endmodule
