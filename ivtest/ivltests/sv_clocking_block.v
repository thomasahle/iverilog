// Test for clocking blocks (SV 14.3)
module test;
  logic clk = 0;
  logic a, b, c;

  // Named clocking block
  clocking ck1 @(posedge clk);
    default input #10ns output #5ns;
    input a;
    output b;
    output #3ns c;
  endclocking

  // Default clocking block (nameless)
  default clocking @(negedge clk);
    default input #1;
  endclocking

  initial begin
    // Just test that clocking blocks are parsed
    $display("PASSED");
    $finish;
  end

endmodule
