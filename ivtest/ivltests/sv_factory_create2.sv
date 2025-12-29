// Test $ivl_factory_create with deep inheritance
// Verifies constructor chaining works correctly

class level0;
  int val0;
  function new();
    val0 = 100;
  endfunction
endclass

class level1 extends level0;
  int val1;
  function new();
    super.new();
    val1 = 200;
  endfunction
endclass

class level2 extends level1;
  int val2;
  function new();
    super.new();
    val2 = 300;
  endfunction

  function void check();
    if (val0 != 100 || val1 != 200 || val2 != 300) begin
      $display("FAILED: values mismatch %0d %0d %0d", val0, val1, val2);
    end else begin
      $display("PASSED");
    end
  endfunction
endclass

module test;
  initial begin
    level0 obj;
    level2 l2;
    string type_name;

    type_name = "level2";
    obj = $ivl_factory_create(type_name);

    if (obj == null) begin
      $display("FAILED: factory create returned null");
      $finish;
    end

    if (!$cast(l2, obj)) begin
      $display("FAILED: cast to level2 failed");
      $finish;
    end

    l2.check();
  end
endmodule
