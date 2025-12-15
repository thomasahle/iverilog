// Test class properties with unpacked arrays
// Each array element should be independent (no aliasing)

class Container;
  int data[4];
  bit [7:0] bytes[2];

  function new();
    data[0] = 10;
    data[1] = 20;
    data[2] = 30;
    data[3] = 40;
    bytes[0] = 8'hAB;
    bytes[1] = 8'hCD;
  endfunction
endclass

module test;
  int pass;
  initial begin
    Container c;
    pass = 1;
    c = new;

    // Check int array elements
    if (c.data[0] !== 10) begin
      $display("FAILED: c.data[0] = %0d, expected 10", c.data[0]);
      pass = 0;
    end
    if (c.data[1] !== 20) begin
      $display("FAILED: c.data[1] = %0d, expected 20", c.data[1]);
      pass = 0;
    end
    if (c.data[2] !== 30) begin
      $display("FAILED: c.data[2] = %0d, expected 30", c.data[2]);
      pass = 0;
    end
    if (c.data[3] !== 40) begin
      $display("FAILED: c.data[3] = %0d, expected 40", c.data[3]);
      pass = 0;
    end

    // Check bit array elements
    if (c.bytes[0] !== 8'hAB) begin
      $display("FAILED: c.bytes[0] = %0h, expected AB", c.bytes[0]);
      pass = 0;
    end
    if (c.bytes[1] !== 8'hCD) begin
      $display("FAILED: c.bytes[1] = %0h, expected CD", c.bytes[1]);
      pass = 0;
    end

    // Test modification
    c.data[1] = 200;
    if (c.data[0] !== 10 || c.data[1] !== 200 || c.data[2] !== 30 || c.data[3] !== 40) begin
      $display("FAILED: Modification affected wrong elements");
      pass = 0;
    end

    if (pass)
      $display("PASSED");
    $finish;
  end
endmodule
