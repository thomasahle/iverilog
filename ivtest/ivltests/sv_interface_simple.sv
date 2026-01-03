// Test simple interface (without modports)
interface simple_bus;
  logic [7:0] data;
  logic valid;
  logic ready;
endinterface

module sender(simple_bus bus);
  initial begin
    bus.data = 8'hAA;
    bus.valid = 1;
    #10;
    bus.valid = 0;
  end
endmodule

module receiver(simple_bus bus);
  logic [7:0] received;

  always @(posedge bus.valid) begin
    received = bus.data;
  end

  initial begin
    bus.ready = 1;
  end
endmodule

module test;
  simple_bus bus();
  sender s(.bus(bus));
  receiver r(.bus(bus));

  int errors = 0;

  initial begin
    #20;
    if (r.received != 8'hAA) begin
      $display("FAILED: received = %h, expected AA", r.received);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
