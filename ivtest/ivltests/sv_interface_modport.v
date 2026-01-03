// Test interface modport port declarations
// This tests the interface_name.modport_name syntax in module ports

interface bus_if;
  logic clk;
  logic [7:0] data;
  logic valid;
  logic ready;

  modport master (
    input clk,
    output data,
    output valid,
    input ready
  );

  modport slave (
    input clk,
    input data,
    input valid,
    output ready
  );
endinterface

// Module using master modport
module sender(bus_if.master bus);
  initial begin
    bus.data = 8'hAB;
    bus.valid = 1;
    #10;
    bus.valid = 0;
  end
endmodule

// Module using slave modport
module receiver(bus_if.slave bus);
  logic [7:0] captured;

  always @(posedge bus.valid) begin
    captured = bus.data;
  end

  initial begin
    bus.ready = 1;
  end
endmodule

module test;
  bus_if bus();
  sender s(.bus(bus));
  receiver r(.bus(bus));

  int errors = 0;

  initial begin
    #20;
    if (r.captured != 8'hAB) begin
      $display("FAILED: captured = %h, expected AB", r.captured);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
