// Test semaphore type recognition
// This tests that the semaphore keyword is recognized as a valid data type
module test;
  semaphore sem;

  initial begin
    // Semaphore declaration should work
    $display("Semaphore type recognized");
    $display("PASSED");
    $finish;
  end
endmodule
