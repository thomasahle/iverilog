// Test super method calls in class hierarchy
// Verifies: super.method() calls parent implementation

module test;

  class Base;
    int value;

    function new();
      value = 10;
    endfunction

    virtual function void process();
      value = value * 2;
      $display("Base::process() called, value=%0d", value);
    endfunction

    virtual function int get_result();
      return value;
    endfunction
  endclass

  class Derived extends Base;
    int extra;

    function new();
      super.new();
      extra = 5;
    endfunction

    virtual function void process();
      // Call parent first
      super.process();
      // Then add derived processing
      value = value + extra;
      $display("Derived::process() called, value=%0d", value);
    endfunction

    virtual function int get_result();
      // Add extra to parent result
      return super.get_result() + extra;
    endfunction
  endclass

  class GrandChild extends Derived;
    int bonus;

    function new();
      super.new();
      bonus = 100;
    endfunction

    virtual function void process();
      super.process();
      value = value + bonus;
      $display("GrandChild::process() called, value=%0d", value);
    endfunction
  endclass

  initial begin
    Base b;
    Derived d;
    GrandChild g;

    // Test Base
    b = new();
    b.process();
    if (b.get_result() != 20) begin
      $display("FAILED: Base result = %0d, expected 20", b.get_result());
      $finish;
    end

    // Test Derived
    d = new();
    d.process();
    // Base: 10*2=20, Derived: 20+5=25
    if (d.get_result() != 30) begin  // 25 + 5 extra
      $display("FAILED: Derived result = %0d, expected 30", d.get_result());
      $finish;
    end

    // Test GrandChild
    g = new();
    g.process();
    // Base: 10*2=20, Derived: 20+5=25, GrandChild: 25+100=125
    if (g.value != 125) begin
      $display("FAILED: GrandChild value = %0d, expected 125", g.value);
      $finish;
    end

    $display("All super calls working correctly");
    $display("PASSED");
    $finish;
  end

endmodule
