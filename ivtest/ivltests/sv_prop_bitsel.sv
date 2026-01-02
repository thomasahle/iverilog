// Test bit-select on class vector properties
module test;

class test_class;
  logic [7:0] data;

  function new();
    data = 8'b00000000;
  endfunction
endclass

initial begin
  test_class obj;
  obj = new();

  $display("Initial data = %b", obj.data);

  // Bit-select assignment
  obj.data[0] = 1'b1;
  $display("After data[0]=1: data = %b", obj.data);

  obj.data[3] = 1'b1;
  $display("After data[3]=1: data = %b", obj.data);

  obj.data[7] = 1'b1;
  $display("After data[7]=1: data = %b", obj.data);

  // Variable bit-select
  for (int i = 1; i < 3; i++) begin
    obj.data[i] = 1'b1;
  end
  $display("After loop: data = %b", obj.data);

  if (obj.data == 8'b10001111) begin
    $display("PASSED: Bit-select on class vector property works!");
  end else begin
    $display("FAILED: Expected 10001111, got %b", obj.data);
  end
end

endmodule
