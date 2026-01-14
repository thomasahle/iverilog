// Minimal reproduction of virtual dispatch + cast bug

class Base;
  // Wrapper that calls virtual method
  function bit call_test(Base rhs);
    $display("call_test: calling test()");
    return test(rhs);
  endfunction

  virtual function bit test(Base rhs);
    $display("Base::test called");
    return 1;
  endfunction
endclass

class Derived extends Base;
  int value;

  function new();
    value = 42;
  endfunction

  virtual function bit test(Base rhs);
    Derived d;
    $display("Derived::test: about to cast");
    if ($cast(d, rhs)) begin
      $display("Derived::test: cast succeeded, value=%0d", d.value);
      return (value == d.value);
    end
    $display("Derived::test: cast failed");
    return 0;
  endfunction
endclass

module top;
  initial begin
    Derived d1, d2;

    d1 = new();
    d2 = new();

    $display("Test 1: Direct call to test()...");
    if (d1.test(d2)) begin
      $display("Test 1: PASSED");
    end else begin
      $display("Test 1: FAILED");
    end

    $display("Test 2: Indirect call through call_test()...");
    if (d1.call_test(d2)) begin
      $display("Test 2: PASSED");
    end else begin
      $display("Test 2: FAILED");
    end

    $finish;
  end
endmodule
