// Test associative array with bit type elements
module test;
  // Associative array with int key and bit[3:0] value
  bit [3:0] assoc_bit[int];
  bit [3:0] val;

  initial begin
    assoc_bit[0] = 4'hA;
    assoc_bit[4] = 4'hF;
    assoc_bit[100] = 4'h5;

    val = assoc_bit[0];
    $display("assoc_bit[0] = %h", val);
    val = assoc_bit[4];
    $display("assoc_bit[4] = %h", val);
    val = assoc_bit[100];
    $display("assoc_bit[100] = %h", val);

    if (assoc_bit[0] == 4'hA && assoc_bit[4] == 4'hF && assoc_bit[100] == 4'h5) begin
      $display("PASSED");
    end else begin
      $display("FAILED");
    end
    $finish;
  end
endmodule
