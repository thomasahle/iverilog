// Test foreach on nested class property arrays
// Pattern: foreach(this.prop.array[i]) { body }

class Config;
  int items[];

  function new(int size);
    items = new[size];
    for (int i = 0; i < size; i++)
      items[i] = (i + 1) * 10;
  endfunction
endclass

class Container;
  Config cfg;

  function new();
    cfg = new(3);
  endfunction

  // Test foreach(cfg.items[i]) where cfg is a property of this class
  function int sum_items();
    int total = 0;
    foreach(cfg.items[i]) begin
      total += cfg.items[i];
    end
    return total;
  endfunction

  function int count_items();
    int count = 0;
    foreach(cfg.items[i]) begin
      count++;
    end
    return count;
  endfunction
endclass

module test;
  initial begin
    Container c;
    int sum, count;

    c = new();

    // Test foreach sum
    sum = c.sum_items();
    if (sum != 60) begin  // 10 + 20 + 30 = 60
      $display("FAILED: sum_items() = %0d, expected 60", sum);
      $finish;
    end

    // Test foreach count
    count = c.count_items();
    if (count != 3) begin
      $display("FAILED: count_items() = %0d, expected 3", count);
      $finish;
    end

    $display("PASSED");
  end
endmodule
