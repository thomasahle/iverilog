// Test config_db set/get functionality
// This test uses the vvp config_db opcodes directly via UVM-style calls

class config_obj;
  int value;
  string name;
  
  function new(int v = 0, string n = "");
    value = v;
    name = n;
  endfunction
endclass

// Minimal config_db implementation to test the vvp opcodes
class config_db #(type T = int);
  static function void set(string context_path, string inst_name, string field_name, T value);
    // This will be compiled to %config_db/set/o opcode
  endfunction
  
  static function bit get(string context_path, string inst_name, string field_name, ref T value);
    // This will be compiled to %config_db/get/o opcode
    return 1;
  endfunction
endclass

module test;
  initial begin
    config_obj cfg_in, cfg_out;
    
    // Create config object
    cfg_in = new(42, "test_config");
    $display("Setting config with value=%0d, name=%s", cfg_in.value, cfg_in.name);
    
    // Set in config_db
    config_db#(config_obj)::set("", "*", "my_config", cfg_in);
    
    // Get from config_db
    if (config_db#(config_obj)::get("", "", "my_config", cfg_out)) begin
      if (cfg_out != null) begin
        $display("Got config with value=%0d, name=%s", cfg_out.value, cfg_out.name);
        if (cfg_out.value == 42) begin
          $display("PASSED");
        end else begin
          $display("FAILED: value mismatch");
        end
      end else begin
        $display("FAILED: got null object");
      end
    end else begin
      $display("FAILED: config_db get returned false");
    end
  end
endmodule
