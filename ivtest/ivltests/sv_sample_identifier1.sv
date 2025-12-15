// Test that 'sample' and 'option' can be used as variable names
// These were previously global keywords that blocked their use as identifiers

module test;
  int sample;      // 'sample' as variable name
  int option;      // 'option' as variable name
  int sample_data;
  int option_value;

  initial begin
    sample = 42;
    option = 100;
    sample_data = sample * 2;
    option_value = option + 1;

    if (sample !== 42) begin
      $display("FAILED: sample = %0d, expected 42", sample);
      $finish;
    end

    if (option !== 100) begin
      $display("FAILED: option = %0d, expected 100", option);
      $finish;
    end

    if (sample_data !== 84) begin
      $display("FAILED: sample_data = %0d, expected 84", sample_data);
      $finish;
    end

    if (option_value !== 101) begin
      $display("FAILED: option_value = %0d, expected 101", option_value);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
