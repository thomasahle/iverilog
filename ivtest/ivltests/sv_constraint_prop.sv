// Test property-to-property constraints in randomize()
module test;

class PropConstraint;
  rand int x;
  rand int y;
  int limit;  // non-rand property

  constraint c_x { x >= 0; x < 10; }
  constraint c_y { y > x; y <= limit; }

  function new();
    limit = 20;
  endfunction
endclass

initial begin
  PropConstraint obj;
  int pass_count = 0;
  int fail_count = 0;
  int i;

  obj = new();

  for (i = 0; i < 20; i++) begin
    if (obj.randomize()) begin
      if (obj.x >= 0 && obj.x < 10 &&
          obj.y > obj.x && obj.y <= obj.limit) begin
        pass_count++;
      end else begin
        $display("FAIL: x=%0d, y=%0d, limit=%0d - constraints violated",
                 obj.x, obj.y, obj.limit);
        fail_count++;
      end
    end else begin
      $display("FAIL: randomize() returned 0");
      fail_count++;
    end
  end

  if (fail_count == 0) begin
    $display("PASSED: %0d randomizations satisfied constraints", pass_count);
  end else begin
    $display("FAILED: %0d failures", fail_count);
  end

  $finish;
end

endmodule
