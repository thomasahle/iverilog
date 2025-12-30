// Test nested class property with randomize() method
// This tests calling randomize() on a property that is a nested class object
// Pattern: outerConfig.innerConfig.randomize()

class InnerConfig;
  rand int value;
  rand bit flag;
  constraint c1 { value >= 0; value < 100; }
endclass

class OuterConfig;
  InnerConfig innerConfig;
  bit hasScoreboard;

  function new();
    innerConfig = new();
  endfunction
endclass

class TestClass;
  OuterConfig outerConfig;
  int errors;

  function new();
    outerConfig = new();
    errors = 0;
  endfunction

  function void run();
    // Test basic nested property randomize
    if (!outerConfig.innerConfig.randomize()) begin
      $display("FAILED: randomize() returned false");
      errors++;
    end

    if (outerConfig.innerConfig.value < 0 || outerConfig.innerConfig.value >= 100) begin
      $display("FAILED: value out of range: %0d", outerConfig.innerConfig.value);
      errors++;
    end

    // Test with inline constraint (constraint not enforced but syntax should work)
    if (!outerConfig.innerConfig.randomize() with { flag == 1; }) begin
      $display("FAILED: randomize() with constraint returned false");
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  endfunction
endclass

module test;
  TestClass t;

  initial begin
    t = new();
    t.run();
  end
endmodule
