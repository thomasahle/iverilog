// Test $countones system function

module test;
  logic [15:0] pselx;
  logic penable;
  int cnt;

  initial begin
    // Test basic countones
    pselx = 16'b0000_0000_0000_0001;
    cnt = $countones(pselx);
    $display("pselx=%b, $countones=%0d", pselx, cnt);
    if (cnt !== 1) $display("FAIL: expected 1");

    // Test with multiple bits
    pselx = 16'b0000_0000_0000_1111;
    cnt = $countones(pselx);
    $display("pselx=%b, $countones=%0d", pselx, cnt);
    if (cnt !== 4) $display("FAIL: expected 4");

    // Test with all ones
    pselx = 16'hFFFF;
    cnt = $countones(pselx);
    $display("pselx=%b, $countones=%0d", pselx, cnt);
    if (cnt !== 16) $display("FAIL: expected 16");

    // Test while loop condition
    pselx = 16'b1;
    penable = 1;

    $display("Testing while condition: pselx=%b, penable=%b", pselx, penable);
    $display("$countones(pselx)=%0d", $countones(pselx));
    $display("$countones(pselx) !== 1: %b", $countones(pselx) !== 1);
    $display("penable !== 1: %b", penable !== 1);
    $display("Full condition: %b", ($countones(pselx) !== 1 || penable !== 1));

    if ($countones(pselx) !== 1 || penable !== 1) begin
      $display("FAIL: Condition should be false (0)");
    end else begin
      $display("PASS: Condition is false as expected");
    end

    $display("PASSED");
  end
endmodule
