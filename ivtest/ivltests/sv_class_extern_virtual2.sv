// Test extern virtual methods with deep inheritance hierarchy
// Tests virtual dispatch through multiple levels of inheritance

class Level1;
  int value;

  extern virtual function int compute();
  extern function int wrapper();

  function new(int v);
    value = v;
  endfunction
endclass

class Level2 extends Level1;
  int multiplier;

  extern virtual function int compute();

  function new(int v, int m);
    super.new(v);
    multiplier = m;
  endfunction
endclass

class Level3 extends Level2;
  int offset;

  extern virtual function int compute();

  function new(int v, int m, int o);
    super.new(v, m);
    offset = o;
  endfunction
endclass

// Out-of-body definitions
function int Level1::compute();
  return value;
endfunction

function int Level1::wrapper();
  // This should dispatch to the actual runtime type's compute()
  return compute();
endfunction

function int Level2::compute();
  return value * multiplier;
endfunction

function int Level3::compute();
  return (value * multiplier) + offset;
endfunction

module test;
  Level1 l1;
  Level2 l2;
  Level3 l3;
  Level1 base_ref;
  int result;

  initial begin
    // Create instances
    l1 = new(10);
    l2 = new(10, 2);
    l3 = new(10, 2, 5);

    // Test direct calls
    result = l1.compute();
    if (result != 10) begin
      $display("FAILED: l1.compute() = %0d, expected 10", result);
      $finish;
    end

    result = l2.compute();
    if (result != 20) begin
      $display("FAILED: l2.compute() = %0d, expected 20", result);
      $finish;
    end

    result = l3.compute();
    if (result != 25) begin
      $display("FAILED: l3.compute() = %0d, expected 25", result);
      $finish;
    end

    // Test wrapper (virtual dispatch through base class method)
    result = l1.wrapper();
    if (result != 10) begin
      $display("FAILED: l1.wrapper() = %0d, expected 10", result);
      $finish;
    end

    result = l2.wrapper();
    if (result != 20) begin
      $display("FAILED: l2.wrapper() = %0d, expected 20", result);
      $finish;
    end

    result = l3.wrapper();
    if (result != 25) begin
      $display("FAILED: l3.wrapper() = %0d, expected 25", result);
      $finish;
    end

    // Test polymorphism through base class reference
    base_ref = l3;
    result = base_ref.compute();
    if (result != 25) begin
      $display("FAILED: base_ref(l3).compute() = %0d, expected 25", result);
      $finish;
    end

    result = base_ref.wrapper();
    if (result != 25) begin
      $display("FAILED: base_ref(l3).wrapper() = %0d, expected 25", result);
      $finish;
    end

    base_ref = l2;
    result = base_ref.wrapper();
    if (result != 20) begin
      $display("FAILED: base_ref(l2).wrapper() = %0d, expected 20", result);
      $finish;
    end

    $display("PASSED");
  end
endmodule
