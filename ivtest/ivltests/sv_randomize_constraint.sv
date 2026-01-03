// Test randomize() with inline constraints
class packet;
  rand int value;
  rand bit [7:0] data;

  function new();
    value = 0;
    data = 0;
  endfunction
endclass

module test;
  packet pkt;
  int errors = 0;
  int i;

  initial begin
    pkt = new();

    // Test randomize with constraint
    for (i = 0; i < 10; i++) begin
      if (!pkt.randomize() with { value >= 0; value <= 100; }) begin
        $display("FAILED: randomize() returned 0");
        errors++;
      end
      if (pkt.value < 0 || pkt.value > 100) begin
        $display("FAILED: value %0d not in range [0,100]", pkt.value);
        errors++;
      end
    end

    // Test randomize with equality constraint
    if (!pkt.randomize() with { value == 42; }) begin
      $display("FAILED: randomize() with equality returned 0");
      errors++;
    end
    if (pkt.value != 42) begin
      $display("FAILED: value %0d, expected 42", pkt.value);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
