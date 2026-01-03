// Test class with array properties
class container;
  int data[4];
  bit [7:0] bytes[$];
  string names[string];

  function new();
    data[0] = 10;
    data[1] = 20;
    data[2] = 30;
    data[3] = 40;
  endfunction

  function int sum();
    int s = 0;
    foreach (data[i])
      s += data[i];
    return s;
  endfunction

  function void add_byte(bit [7:0] b);
    bytes.push_back(b);
  endfunction
endclass

module test;
  container c;
  int errors = 0;

  initial begin
    c = new();

    // Test fixed array property
    if (c.data[0] != 10 || c.data[3] != 40) begin
      $display("FAILED: data[0]=%0d, data[3]=%0d", c.data[0], c.data[3]);
      errors++;
    end

    // Test sum method with foreach
    if (c.sum() != 100) begin
      $display("FAILED: sum = %0d, expected 100", c.sum());
      errors++;
    end

    // Modify array element
    c.data[1] = 25;
    if (c.data[1] != 25) begin
      $display("FAILED: modified data[1] = %0d", c.data[1]);
      errors++;
    end

    // Test queue property
    c.add_byte(8'hAA);
    c.add_byte(8'hBB);
    if (c.bytes.size() != 2) begin
      $display("FAILED: bytes.size() = %0d", c.bytes.size());
      errors++;
    end
    if (c.bytes[0] != 8'hAA) begin
      $display("FAILED: bytes[0] = %h", c.bytes[0]);
      errors++;
    end

    // Test assoc array property
    c.names["first"] = "John";
    c.names["last"] = "Doe";
    if (c.names.size() != 2) begin
      $display("FAILED: names.size() = %0d", c.names.size());
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
