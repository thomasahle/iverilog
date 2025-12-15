// Test static method calls inside fork/join blocks
// Tests the statement merging logic for fork/join variants

class counter;
  static int value = 0;

  static function void increment();
    value = value + 1;
  endfunction

  static function void add(int n);
    value = value + n;
  endfunction

  static function int get();
    return value;
  endfunction

  static function void reset();
    value = 0;
  endfunction
endclass

module test;
  int errors = 0;

  initial begin
    // Test static call in fork/join
    counter::reset();
    fork
      counter::add(10);
      counter::add(20);
    join
    if (counter::get() != 30) begin
      $display("FAILED: fork/join result=%0d, expected 30", counter::get());
      errors = errors + 1;
    end

    // Test static call in fork/join_any
    counter::reset();
    fork
      begin
        #5;
        counter::add(100);
      end
      begin
        #10;
        counter::add(200);
      end
    join_any
    #1; // Small delay to let first process complete
    if (counter::get() != 100) begin
      $display("FAILED: fork/join_any result=%0d, expected 100", counter::get());
      errors = errors + 1;
    end
    #10; // Wait for second process

    // Test static call in fork/join_none
    counter::reset();
    fork
      begin
        #5;
        counter::add(1000);
      end
    join_none
    #1;
    if (counter::get() != 0) begin
      $display("FAILED: fork/join_none immediate result=%0d, expected 0", counter::get());
      errors = errors + 1;
    end
    #10;
    if (counter::get() != 1000) begin
      $display("FAILED: fork/join_none delayed result=%0d, expected 1000", counter::get());
      errors = errors + 1;
    end

    if (errors == 0) begin
      $display("PASSED");
    end else begin
      $display("FAILED: %0d errors", errors);
    end
    $finish;
  end
endmodule
