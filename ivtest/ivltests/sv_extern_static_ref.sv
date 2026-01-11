// Test extern static function with ref parameter
// Based on APB AVIP converter pattern

class Converter;
  extern static function void to_class(input int in_val, ref int out_val);
endclass

function void Converter::to_class(input int in_val, ref int out_val);
  out_val = in_val * 2;
endfunction

module test;
  initial begin
    int x, y;
    x = 10;
    y = 0;

    Converter::to_class(x, y);

    if (y == 20)
      $display("PASSED");
    else
      $display("FAILED: y=%0d, expected 20", y);
    $finish;
  end
endmodule
