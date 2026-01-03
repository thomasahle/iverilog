// Test static class members
class counter;
  static int count = 0;
  int instance_id;

  function new();
    count++;
    instance_id = count;
  endfunction

  static function int get_count();
    return count;
  endfunction

  function int get_id();
    return instance_id;
  endfunction
endclass

module test;
  counter c1, c2, c3;
  int errors = 0;

  initial begin
    // Check initial count
    if (counter::get_count() != 0) begin
      $display("FAILED: initial count is %0d, expected 0", counter::get_count());
      errors++;
    end

    // Create instances
    c1 = new();
    if (c1.get_id() != 1) begin
      $display("FAILED: c1.id = %0d, expected 1", c1.get_id());
      errors++;
    end
    if (counter::get_count() != 1) begin
      $display("FAILED: count after c1 = %0d, expected 1", counter::get_count());
      errors++;
    end

    c2 = new();
    if (c2.get_id() != 2) begin
      $display("FAILED: c2.id = %0d, expected 2", c2.get_id());
      errors++;
    end

    c3 = new();
    if (counter::get_count() != 3) begin
      $display("FAILED: count after c3 = %0d, expected 3", counter::get_count());
      errors++;
    end

    // Verify count accessible from instance
    if (c1.count != 3) begin
      $display("FAILED: c1.count = %0d, expected 3", c1.count);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
