// Test that constraints are inherited from parent classes
// This verifies that when a derived class extends a base class with constraints,
// the base class constraints are properly enforced during randomize()

class base;
  rand int value;

  constraint base_c {
    value >= 0;
    value < 100;
  }
endclass

class derived extends base;
  // Inherit base_c constraint from base class
  rand int extra;

  constraint derived_c {
    extra > 0;
    extra < 50;
  }
endclass

class grandchild extends derived;
  // Inherit both base_c and derived_c
  rand int level;

  constraint grandchild_c {
    level >= 10;
    level <= 20;
  }
endclass

module test;
  initial begin
    base b;
    derived d;
    grandchild g;
    int pass = 1;

    // Test base class constraints
    b = new();
    repeat(10) begin
      void'(b.randomize());
      if (b.value < 0 || b.value >= 100) begin
        $display("FAIL: base value=%0d out of range [0,100)", b.value);
        pass = 0;
      end
    end

    // Test derived class inherits base constraints
    d = new();
    repeat(10) begin
      void'(d.randomize());
      if (d.value < 0 || d.value >= 100) begin
        $display("FAIL: derived.value=%0d out of base range [0,100)", d.value);
        pass = 0;
      end
      if (d.extra <= 0 || d.extra >= 50) begin
        $display("FAIL: derived.extra=%0d out of range (0,50)", d.extra);
        pass = 0;
      end
    end

    // Test grandchild inherits both parent and grandparent constraints
    g = new();
    repeat(10) begin
      void'(g.randomize());
      if (g.value < 0 || g.value >= 100) begin
        $display("FAIL: grandchild.value=%0d out of base range [0,100)", g.value);
        pass = 0;
      end
      if (g.extra <= 0 || g.extra >= 50) begin
        $display("FAIL: grandchild.extra=%0d out of derived range (0,50)", g.extra);
        pass = 0;
      end
      if (g.level < 10 || g.level > 20) begin
        $display("FAIL: grandchild.level=%0d out of range [10,20]", g.level);
        pass = 0;
      end
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
