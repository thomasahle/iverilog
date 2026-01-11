// Test case statement with struct enum member
// Verifies: case(struct.enumMember) pattern works with direct access
// Note: struct_member.name() is a known limitation - use temp variable for .name()

module test;

  typedef enum int {
    MODE_IDLE = 0,
    MODE_RUN = 1,
    MODE_STOP = 2
  } mode_e;

  typedef struct {
    mode_e mode;
    int data;
  } config_t;

  config_t cfg;
  string result;

  initial begin
    // Test case with struct enum member - direct access works
    cfg.mode = MODE_IDLE;
    cfg.data = 100;

    case (cfg.mode)
      MODE_IDLE: result = "idle";
      MODE_RUN:  result = "run";
      MODE_STOP: result = "stop";
      default:   result = "unknown";
    endcase

    $display("Mode value: %0d, result: %s", cfg.mode, result);
    if (result != "idle") begin
      $display("FAILED: Expected 'idle' for MODE_IDLE");
      $finish;
    end

    // Change mode
    cfg.mode = MODE_RUN;
    case (cfg.mode)
      MODE_IDLE: result = "idle";
      MODE_RUN:  result = "run";
      MODE_STOP: result = "stop";
      default:   result = "unknown";
    endcase

    if (result != "run") begin
      $display("FAILED: Expected 'run' for MODE_RUN");
      $finish;
    end

    // Test MODE_STOP
    cfg.mode = MODE_STOP;
    case (cfg.mode)
      MODE_IDLE: result = "idle";
      MODE_RUN:  result = "run";
      MODE_STOP: result = "stop";
      default:   result = "unknown";
    endcase

    if (result != "stop") begin
      $display("FAILED: Expected 'stop' for MODE_STOP");
      $finish;
    end

    $display("PASSED");
    $finish;
  end

endmodule
