// Test constant part-select on struct array member elements
// Pattern: struct.arr[i][high:low]

module test;
  parameter DATA_WIDTH = 8;

  typedef struct {
    bit [DATA_WIDTH-1:0] data[4];  // Array of packed values
    int count;
  } container_t;

  initial begin
    container_t c;
    bit [3:0] nibble;
    int pass = 1;

    // Initialize
    c.data[0] = 8'hAB;
    c.data[1] = 8'hCD;
    c.data[2] = 8'hEF;
    c.data[3] = 8'h12;

    // Test 1: Part-select low nibble from element 0
    nibble = c.data[0][3:0];  // Should be 4'hB
    if (nibble !== 4'hB) begin
      $display("FAILED: Test 1 - nibble = %h, expected B", nibble);
      pass = 0;
    end

    // Test 2: Part-select high nibble from element 0
    nibble = c.data[0][7:4];  // Should be 4'hA
    if (nibble !== 4'hA) begin
      $display("FAILED: Test 2 - nibble = %h, expected A", nibble);
      pass = 0;
    end

    // Test 3: Part-select from element 1
    nibble = c.data[1][3:0];  // Should be 4'hD
    if (nibble !== 4'hD) begin
      $display("FAILED: Test 3 - nibble = %h, expected D", nibble);
      pass = 0;
    end

    // Test 4: Variable index with part-select
    for (int i = 0; i < 4; i++) begin
      nibble = c.data[i][3:0];
      case (i)
        0: if (nibble !== 4'hB) begin $display("FAILED: Test 4a - nibble = %h", nibble); pass = 0; end
        1: if (nibble !== 4'hD) begin $display("FAILED: Test 4b - nibble = %h", nibble); pass = 0; end
        2: if (nibble !== 4'hF) begin $display("FAILED: Test 4c - nibble = %h", nibble); pass = 0; end
        3: if (nibble !== 4'h2) begin $display("FAILED: Test 4d - nibble = %h", nibble); pass = 0; end
      endcase
    end

    if (pass)
      $display("PASSED");
  end
endmodule
