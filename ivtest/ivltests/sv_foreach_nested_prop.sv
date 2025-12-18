// Test for foreach on nested class properties: foreach(this.prop.array[i])
// This tests the fix for iterating over dynamic array properties accessed
// through a property of 'this'.

class Config;
  int items[];

  function new();
    items = new[3];
    items[0] = 10;
    items[1] = 20;
    items[2] = 30;
  endfunction
endclass

class Container;
  Config cfg;
  int result;

  function new();
    cfg = new();
    result = 0;
  endfunction

  // Test foreach(cfg.items[i]) where cfg is a property of this class
  function void compute_sum();
    foreach(cfg.items[i]) begin
      result += cfg.items[i];
    end
  endfunction
endclass

module test;
  Container c;

  initial begin
    c = new();
    c.compute_sum();

    if (c.result == 60) begin
      $display("PASSED: foreach on nested property works (sum=%0d)", c.result);
    end else begin
      $display("FAILED: expected sum=60, got %0d", c.result);
    end

    $finish;
  end
endmodule
