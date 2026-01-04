// Test basic class-level constraints
// Class-level constraints with simple comparisons work correctly

module test;
  class MyClass;
    rand int x;
    rand int y;
    constraint range_x { x >= 10; x <= 50; }
    constraint range_y { y > x; }  // Relational between variables
  endclass

  MyClass obj;
  int pass_count = 0;

  initial begin
    obj = new();

    // Test class-level constraints
    for (int i = 0; i < 10; i++) begin
      if (!obj.randomize()) begin
        $display("FAILED: randomize returned false");
        $finish;
      end
      
      if (obj.x >= 10 && obj.x <= 50) begin
        pass_count++;
      end else begin
        $display("FAILED: x=%0d outside range [10:50]", obj.x);
        $finish;
      end
    end

    if (pass_count == 10) begin
      $display("PASSED");
    end else begin
      $display("FAILED: only %0d/10 iterations passed", pass_count);
    end
  end
endmodule
