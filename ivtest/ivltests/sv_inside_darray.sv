// Test inside constraint with dynamic array property
// Verifies that "x inside {arr}" works when arr is a dynamic array class property

class Test;
  rand bit [7:0] value;
  bit [7:0] allowed_vals[];

  function new();
    allowed_vals = new[3];
    allowed_vals[0] = 10;
    allowed_vals[1] = 20;
    allowed_vals[2] = 30;
  endfunction
endclass

module test;
  Test t;
  int count_in, count_out;

  initial begin
    t = new();
    count_in = 0;
    count_out = 0;

    // Test: value inside dynamic array property (property chain t.allowed_vals)
    repeat(100) begin
      if (!t.randomize() with {
        value inside {t.allowed_vals};
      }) begin
        $display("FAIL: randomize failed");
      end else begin
        if (t.value == 10 || t.value == 20 || t.value == 30)
          count_in++;
        else begin
          count_out++;
          $display("Got unexpected value: %0d", t.value);
        end
      end
    end

    $display("Results: in=%0d, out=%0d", count_in, count_out);
    if (count_out == 0 && count_in == 100)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end
endmodule
