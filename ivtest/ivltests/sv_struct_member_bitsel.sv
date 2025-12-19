// Test bit-select on packed member of unpacked struct
// Tests: struct.packed_member[bit_idx] = value
module test;
  typedef struct {
    bit [7:0] data;
    bit [3:0] strb;
    bit flag;
  } my_struct_t;

  my_struct_t s;
  integer i;
  int count;
  int errors;

  initial begin
    errors = 0;
    s.data = 8'h00;
    s.strb = 4'b0000;
    s.flag = 1'b0;

    // Bit-select assignment with constant index
    s.strb[0] = 1'b1;
    if (s.strb !== 4'b0001) begin
      $display("FAILED: s.strb[0]=1 gave %b, expected 0001", s.strb);
      errors = errors + 1;
    end

    s.strb[2] = 1'b1;
    if (s.strb !== 4'b0101) begin
      $display("FAILED: s.strb[2]=1 gave %b, expected 0101", s.strb);
      errors = errors + 1;
    end

    s.data[7] = 1'b1;
    if (s.data !== 8'h80) begin
      $display("FAILED: s.data[7]=1 gave %h, expected 80", s.data);
      errors = errors + 1;
    end

    s.data[0] = 1'b1;
    if (s.data !== 8'h81) begin
      $display("FAILED: s.data[0]=1 gave %h, expected 81", s.data);
      errors = errors + 1;
    end

    // Variable bit-select read (loop)
    count = 0;
    for (i = 0; i < 4; i = i + 1) begin
      if (s.strb[i]) count = count + 1;
    end
    if (count !== 2) begin
      $display("FAILED: Count of 1s in strb=%b should be 2, got %0d", s.strb, count);
      errors = errors + 1;
    end

    if (errors == 0) begin
      $display("PASSED");
    end else begin
      $display("FAILED: %0d errors", errors);
    end

    $finish;
  end
endmodule
