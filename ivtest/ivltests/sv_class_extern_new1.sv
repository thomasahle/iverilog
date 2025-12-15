// Test extern constructor with 'endfunction : new' label syntax
// The 'new' keyword after endfunction requires special handling since
// 'new' is K_new (a keyword), not IDENTIFIER

class Config;
  string name;
  int width;
  int height;

  extern function new(string n = "default", int w = 80, int h = 24);
endclass

function Config::new(string n = "default", int w = 80, int h = 24);
  name = n;
  width = w;
  height = h;
  $display("Config::new(%s, %0d, %0d)", name, width, height);
endfunction : new  // This 'new' label requires special parser handling

module test;
  initial begin
    Config cfg1, cfg2, cfg3;

    // Test with all defaults
    cfg1 = new();
    if (cfg1.name != "default" || cfg1.width != 80 || cfg1.height != 24) begin
      $display("FAILED: cfg1 defaults incorrect");
      $finish;
    end

    // Test with custom name
    cfg2 = new("custom");
    if (cfg2.name != "custom" || cfg2.width != 80) begin
      $display("FAILED: cfg2 values incorrect");
      $finish;
    end

    // Test with all custom values
    cfg3 = new("full", 120, 40);
    if (cfg3.name != "full" || cfg3.width != 120 || cfg3.height != 40) begin
      $display("FAILED: cfg3 values incorrect");
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
