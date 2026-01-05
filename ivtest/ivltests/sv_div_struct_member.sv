// Test division with struct member access
module test;
  typedef struct {
    int wordSelectPeriod;
    int clockPeriod;
  } config_t;

  initial begin
    config_t cfgStruct;
    int result;

    cfgStruct.wordSelectPeriod = 64;
    cfgStruct.clockPeriod = 100;

    // Division of struct member by constant
    result = cfgStruct.wordSelectPeriod / 2;
    $display("wordSelectPeriod/2 = %0d (expected 32)", result);

    if (result == 32)
      $display("PASSED");
    else
      $display("FAILED: got %0d, expected 32", result);
  end
endmodule
