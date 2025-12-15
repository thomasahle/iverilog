// Test: multiple interface instances
// Each interface instance should be independent

interface SimpleIface;
  logic [7:0] data;
endinterface

module test;
  // Multiple interface instances (separate declarations)
  SimpleIface if1();
  SimpleIface if2();
  SimpleIface if3();

  initial begin
    if1.data = 8'h11;
    if2.data = 8'h22;
    if3.data = 8'h33;
    #1;
    if (if1.data !== 8'h11 || if2.data !== 8'h22 || if3.data !== 8'h33) begin
      $display("FAILED: if1=%h if2=%h if3=%h", if1.data, if2.data, if3.data);
      $finish;
    end
    $display("PASSED");
  end
endmodule
