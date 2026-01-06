// Test simple associative array with int element type
module test;
  // Simple associative array with int key and int value
  int simple_assoc[int];

  initial begin
    simple_assoc[0] = 10;
    simple_assoc[4] = 15;
    simple_assoc[100] = 5;

    $display("simple_assoc[0] = %0d", simple_assoc[0]);
    $display("simple_assoc[4] = %0d", simple_assoc[4]);
    $display("simple_assoc[100] = %0d", simple_assoc[100]);

    if (simple_assoc[0] == 10 && simple_assoc[4] == 15 && simple_assoc[100] == 5) begin
      $display("PASSED");
    end else begin
      $display("FAILED");
    end
    $finish;
  end
endmodule
