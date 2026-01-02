// Test increment/decrement on class properties
module test;

class test_class;
  int count;
  int value;

  function new();
    count = 0;
    value = 10;
  endfunction
endclass

initial begin
  test_class obj;
  int result;
  obj = new();

  $display("Initial count = %0d, value = %0d", obj.count, obj.value);

  // Pre-increment
  result = ++obj.count;
  if (obj.count != 1 || result != 1) begin
    $display("FAILED: ++obj.count: expected count=1, result=1, got count=%0d, result=%0d",
             obj.count, result);
    $finish;
  end

  // Post-increment
  result = obj.count++;
  if (obj.count != 2 || result != 1) begin
    $display("FAILED: obj.count++: expected count=2, result=1, got count=%0d, result=%0d",
             obj.count, result);
    $finish;
  end

  // Pre-decrement
  result = --obj.value;
  if (obj.value != 9 || result != 9) begin
    $display("FAILED: --obj.value: expected value=9, result=9, got value=%0d, result=%0d",
             obj.value, result);
    $finish;
  end

  // Post-decrement
  result = obj.value--;
  if (obj.value != 8 || result != 9) begin
    $display("FAILED: obj.value--: expected value=8, result=9, got value=%0d, result=%0d",
             obj.value, result);
    $finish;
  end

  $display("PASSED");
end

endmodule
