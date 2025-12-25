// Test variable lifetime override (automatic/static)
// IEEE 1800-2012 Section 6.21

module test;
  
  // Task with automatic variable override
  task test_automatic();
    automatic logic [31:0] auto_var = 32'hDEADBEEF;
    automatic int auto_int = 42;
    $display("auto_var = %h, auto_int = %0d", auto_var, auto_int);
  endtask
  
  // Task with static variable
  task automatic test_static_in_auto();
    static int call_count = 0;
    call_count++;
    $display("call_count = %0d", call_count);
  endtask
  
  // Function with automatic variable
  function automatic int get_value();
    automatic int temp = 100;
    return temp;
  endfunction
  
  // Interface-like module with automatic variables  
  task drive_data();
    automatic logic [7:0] data = 8'hAB;
    automatic logic valid = 1'b1;
    $display("data = %h, valid = %b", data, valid);
  endtask
  
  initial begin
    test_automatic();
    test_static_in_auto();
    test_static_in_auto();
    drive_data();
    $display("get_value = %0d", get_value());
    $display("PASSED - Variable lifetime override parsed successfully");
    $finish;
  end
endmodule
