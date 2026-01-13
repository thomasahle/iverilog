// Test simple let declarations without arguments
module test;
  // Simple constants using let
  let zero = 0;
  let one = 1;
  let meaning_of_life = 42;

  // Expression let
  let four = 2 + 2;

  initial begin
    int result;

    // Use simple let
    result = zero;
    $display("zero = %0d", result);
    if (result !== 0) begin
      $display("FAILED: zero should be 0");
      $finish;
    end

    result = one;
    $display("one = %0d", result);
    if (result !== 1) begin
      $display("FAILED: one should be 1");
      $finish;
    end

    result = meaning_of_life;
    $display("meaning_of_life = %0d", result);
    if (result !== 42) begin
      $display("FAILED: meaning_of_life should be 42");
      $finish;
    end

    result = four;
    $display("four = %0d", result);
    if (result !== 4) begin
      $display("FAILED: four should be 4");
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
