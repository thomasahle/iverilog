// Test class virtual method override
class base;
  virtual function string get_name();
    return "base";
  endfunction

  virtual function int get_value();
    return 0;
  endfunction
endclass

class derived extends base;
  function string get_name();
    return "derived";
  endfunction

  function int get_value();
    return 42;
  endfunction
endclass

module test;
  base b;
  derived d;
  int errors = 0;

  initial begin
    // Test base class
    b = new();
    if (b.get_name() != "base") begin
      $display("FAILED: base.get_name() = %s", b.get_name());
      errors++;
    end
    if (b.get_value() != 0) begin
      $display("FAILED: base.get_value() = %0d", b.get_value());
      errors++;
    end

    // Test derived class
    d = new();
    if (d.get_name() != "derived") begin
      $display("FAILED: derived.get_name() = %s", d.get_name());
      errors++;
    end
    if (d.get_value() != 42) begin
      $display("FAILED: derived.get_value() = %0d", d.get_value());
      errors++;
    end

    // Test polymorphism - derived assigned to base
    b = d;
    if (b.get_name() != "derived") begin
      $display("FAILED: polymorphic get_name() = %s, expected derived", b.get_name());
      errors++;
    end
    if (b.get_value() != 42) begin
      $display("FAILED: polymorphic get_value() = %0d, expected 42", b.get_value());
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
