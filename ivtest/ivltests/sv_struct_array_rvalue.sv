// Test struct with unpacked array member rvalue access
// This tests accessing my_struct.arr[i] as an rvalue

module test;
  typedef struct {
    logic [7:0] header;
    logic [31:0] data[4];  // Unpacked array member
    logic [7:0] footer;
  } packet_t;

  packet_t pkt;
  logic [31:0] read_val;
  int i;
  int errors;

  initial begin
    errors = 0;

    // Initialize the struct
    pkt.header = 8'hAA;
    pkt.footer = 8'h55;
    for (i = 0; i < 4; i++) begin
      pkt.data[i] = 32'h1000_0000 + i * 32'h100;
    end

    // Test 1: Constant index access
    read_val = pkt.data[0];
    if (read_val !== 32'h1000_0000) begin
      $display("FAILED: Test 1 - pkt.data[0] = %h, expected 10000000", read_val);
      errors++;
    end

    read_val = pkt.data[2];
    if (read_val !== 32'h1000_0200) begin
      $display("FAILED: Test 2 - pkt.data[2] = %h, expected 10000200", read_val);
      errors++;
    end

    // Test 2: Variable index access
    for (i = 0; i < 4; i++) begin
      read_val = pkt.data[i];
      if (read_val !== 32'h1000_0000 + i * 32'h100) begin
        $display("FAILED: Test 3 - pkt.data[%0d] = %h, expected %h",
                 i, read_val, 32'h1000_0000 + i * 32'h100);
        errors++;
      end
    end

    // Test 3: Use in expression
    if (pkt.data[1] + pkt.data[3] !== 32'h2000_0400) begin
      $display("FAILED: Test 4 - sum = %h, expected 20000400",
               pkt.data[1] + pkt.data[3]);
      errors++;
    end

    // Test 4: Assignment using array element
    read_val = pkt.data[0] | pkt.data[1];
    if (read_val !== 32'h1000_0100) begin
      $display("FAILED: Test 5 - OR result = %h, expected 10000100", read_val);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);

    $finish;
  end
endmodule
