// Test part-select on class vector properties
module test;

class test_class;
  logic [15:0] data;

  function new();
    data = 16'h0000;
  endfunction
endclass

initial begin
  test_class obj;
  obj = new();

  $display("Initial data = %h", obj.data);

  // Constant part-select [msb:lsb]
  obj.data[3:0] = 4'hA;
  $display("After data[3:0]=A: data = %h", obj.data);

  obj.data[7:4] = 4'hB;
  $display("After data[7:4]=B: data = %h", obj.data);

  obj.data[15:8] = 8'hCD;
  $display("After data[15:8]=CD: data = %h", obj.data);

  // Indexed part-select [base +: width]
  obj.data = 16'h0000;
  obj.data[0 +: 4] = 4'h5;
  $display("After data[0 +: 4]=5: data = %h", obj.data);

  obj.data[4 +: 4] = 4'h6;
  $display("After data[4 +: 4]=6: data = %h", obj.data);

  if (obj.data == 16'h0065) begin
    $display("PASSED: Part-select on class vector property works!");
  end else begin
    $display("FAILED: Expected 0065, got %h", obj.data);
  end
end

endmodule
