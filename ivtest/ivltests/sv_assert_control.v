// Test assertion control system tasks
// These tasks are stubs in Icarus - they compile and run but don't
// actually control assertion behavior since assertions compile to
// procedural code.

module test;
  int count = 0;

  initial begin
    // Test that all assertion control tasks compile
    $assertoff;           // Turn off assertions
    $assertoff(0);        // Turn off in scope 0
    $assertoff(0, test);  // Turn off in specific scope

    $asserton;            // Turn on assertions
    $asserton(0);
    $asserton(0, test);

    $assertkill;          // Kill current assertions
    $assertkill(0);
    $assertkill(0, test);

    $assertpasson;        // Enable pass action blocks
    $assertpasson(0);

    $assertpassoff;       // Disable pass action blocks
    $assertpassoff(0);

    $assertfailon;        // Enable fail action blocks
    $assertfailon(0);

    $assertfailoff;       // Disable fail action blocks
    $assertfailoff(0);

    $assertnonvacuouson;  // Enable non-vacuous checking
    $assertnonvacuouson(0);

    $assertvacuousoff;    // Disable vacuous pass reporting
    $assertvacuousoff(0);

    $display("PASSED");
  end
endmodule
