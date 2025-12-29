// Test foreach on struct member packed arrays in class properties
// This tests that foreach can iterate over packed array members within
// struct class properties.

module test;
  typedef struct packed {
    logic [3:0][7:0] data;
  } packet_t;

  class MyClass;
    packet_t pkt;

    function void init();
      pkt = 32'h0;
      foreach (pkt.data[i]) begin
        pkt.data[i] = i + 1;
      end
    endfunction

    function bit check();
      foreach (pkt.data[i]) begin
        if (pkt.data[i] !== i + 1) return 0;
      end
      return 1;
    endfunction
  endclass

  initial begin
    MyClass obj = new();
    obj.init();

    $display("pkt=%h", obj.pkt);
    $display("data[0]=%h data[1]=%h data[2]=%h data[3]=%h",
             obj.pkt.data[0], obj.pkt.data[1], obj.pkt.data[2], obj.pkt.data[3]);

    if (obj.check())
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
