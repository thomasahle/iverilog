// Test foreach on packed vector class property
// This tests the case from UART AVIP: foreach(this.transmissionData[i])

module test;

  class DataHolder;
    logic [7:0] data;

    function new();
      data = 8'hA5;  // 10100101
    endfunction

    function void print_bits();
      // Test foreach with explicit this.property
      foreach(this.data[i]) begin
        $display("this.data[%0d] = %b", i, this.data[i]);
      end
    endfunction

    function void print_bits_implicit();
      // Test foreach with implicit this (just property name)
      foreach(data[i]) begin
        $display("data[%0d] = %b", i, data[i]);
      end
    endfunction
  endclass

  DataHolder dh;

  initial begin
    dh = new();

    $display("Testing foreach with explicit this.data:");
    dh.print_bits();

    $display("\nTesting foreach with implicit data:");
    dh.print_bits_implicit();

    $display("PASSED");
  end

endmodule
