// Test property + constant offset in constraints
// e.g., y >= x and y <= x + 10

class Item;
  rand int x;
  rand int y;

  // Constrain y to be in range [x, x+10]
  constraint c1 { y >= x; }
  constraint c2 { y <= x + 10; }
endclass

module test;
  Item item;
  int pass_count = 0;
  int total = 20;

  initial begin
    item = new();

    // Test with random x values
    for (int i = 0; i < total; i++) begin
      void'(item.randomize());

      if (item.y >= item.x && item.y <= item.x + 10) begin
        pass_count++;
      end else begin
        $display("FAIL: x=%0d, y=%0d, y should be in [%0d, %0d]",
                 item.x, item.y, item.x, item.x + 10);
      end
    end

    // Test with fixed x value using rand_mode
    item.x.rand_mode(0);
    item.x = 50;

    for (int i = 0; i < total; i++) begin
      void'(item.randomize());

      if (item.y >= 50 && item.y <= 60) begin
        pass_count++;
      end else begin
        $display("FAIL with fixed x=50: y=%0d, should be in [50, 60]", item.y);
      end
    end

    if (pass_count == total * 2) begin
      $display("PASSED");
    end else begin
      $display("FAILED: %0d/%0d passed", pass_count, total * 2);
    end
  end
endmodule
