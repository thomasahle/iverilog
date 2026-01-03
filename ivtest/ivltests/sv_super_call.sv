// Test super method calls
class base;
  int value;

  function new(int v = 0);
    value = v;
  endfunction

  virtual function int compute();
    return value;
  endfunction

  virtual function string describe();
    return $sformatf("base(%0d)", value);
  endfunction
endclass

class derived extends base;
  int multiplier;

  function new(int v, int m);
    super.new(v);
    multiplier = m;
  endfunction

  virtual function int compute();
    return super.compute() * multiplier;
  endfunction

  virtual function string describe();
    return {super.describe(), $sformatf(" x %0d", multiplier)};
  endfunction
endclass

module test;
  base b;
  derived d;
  int errors = 0;

  initial begin
    // Test derived class
    d = new(10, 3);
    if (d.value != 10) begin
      $display("FAILED: d.value = %0d, expected 10", d.value);
      errors++;
    end
    if (d.multiplier != 3) begin
      $display("FAILED: d.multiplier = %0d, expected 3", d.multiplier);
      errors++;
    end

    // Test super.compute() call
    if (d.compute() != 30) begin
      $display("FAILED: d.compute() = %0d, expected 30", d.compute());
      errors++;
    end

    // Test super.describe() call
    if (d.describe() != "base(10) x 3") begin
      $display("FAILED: d.describe() = %s", d.describe());
      errors++;
    end

    // Test base class
    b = new(5);
    if (b.compute() != 5) begin
      $display("FAILED: b.compute() = %0d, expected 5", b.compute());
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
