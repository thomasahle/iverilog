// UVM Macros for Icarus Verilog
// Simplified macro definitions for basic UVM functionality

`ifndef UVM_MACROS_SVH
`define UVM_MACROS_SVH

// ============================================================================
// Reporting Macros
// Note: These are wrapped in begin/end to be self-contained statements
// that don't require a trailing semicolon (for compatibility with typical usage)
// ============================================================================

`define uvm_info(ID, MSG, VERBOSITY) \
  begin \
    $display("UVM_INFO @ %0t: %s [%s] %s", $time, this.get_full_name(), ID, MSG); \
  end

`define uvm_warning(ID, MSG) \
  begin \
    $display("UVM_WARNING @ %0t: %s [%s] %s", $time, this.get_full_name(), ID, MSG); \
  end

`define uvm_error(ID, MSG) \
  begin \
    $display("UVM_ERROR @ %0t: %s [%s] %s", $time, this.get_full_name(), ID, MSG); \
  end

`define uvm_fatal(ID, MSG) \
  begin \
    $display("UVM_FATAL @ %0t: %s [%s] %s", $time, this.get_full_name(), ID, MSG); \
    $finish; \
  end

// ============================================================================
// Component Registration Macros
// ============================================================================

// Register a component with the factory
`define uvm_component_utils(T) \
  typedef uvm_component_registry #(T, `"T`") type_id; \
  static function uvm_factory_proxy get_type(); \
    return null; \
  endfunction \
  virtual function string get_type_name(); \
    return `"T`"; \
  endfunction

`define uvm_component_utils_begin(T) \
  typedef uvm_component_registry #(T, `"T`") type_id; \
  static function uvm_factory_proxy get_type(); \
    return null; \
  endfunction \
  virtual function string get_type_name(); \
    return `"T`"; \
  endfunction

`define uvm_component_utils_end

// ============================================================================
// Object Registration Macros
// ============================================================================

// Register an object (non-component) with the factory
`define uvm_object_utils(T) \
  typedef uvm_object_registry #(T, `"T`") type_id; \
  static function uvm_factory_proxy get_type(); \
    return null; \
  endfunction \
  virtual function string get_type_name(); \
    return `"T`"; \
  endfunction

`define uvm_object_utils_begin(T) \
  typedef uvm_object_registry #(T, `"T`") type_id; \
  static function uvm_factory_proxy get_type(); \
    return null; \
  endfunction \
  virtual function string get_type_name(); \
    return `"T`"; \
  endfunction

`define uvm_object_utils_end

// ============================================================================
// Field Automation Macros (simplified - no-ops for now)
// ============================================================================

`define uvm_field_int(ARG, FLAG)
`define uvm_field_object(ARG, FLAG)
`define uvm_field_string(ARG, FLAG)
`define uvm_field_enum(T, ARG, FLAG)
`define uvm_field_array_int(ARG, FLAG)
`define uvm_field_queue_int(ARG, FLAG)
`define uvm_field_sarray_int(ARG, FLAG)

// Field flags
`define UVM_ALL_ON       'hFFF
`define UVM_DEFAULT      'hFFF
`define UVM_NOCOMPARE    'h001
`define UVM_NOPRINT      'h002
`define UVM_NOCOPY       'h004
`define UVM_NOPACK       'h008
`define UVM_NORECORD     'h010
`define UVM_DEEP         'h020
`define UVM_SHALLOW      'h040
`define UVM_REFERENCE    'h080
`define UVM_PHYSICAL     'h100
`define UVM_ABSTRACT     'h200
`define UVM_READONLY     'h400

// ============================================================================
// Sequence Macros
// ============================================================================

// Start item on sequencer
`define uvm_do(SEQ_OR_ITEM) \
  begin \
    SEQ_OR_ITEM = new(`"SEQ_OR_ITEM`"); \
    start_item(SEQ_OR_ITEM); \
    if (!SEQ_OR_ITEM.randomize()) begin \
      `uvm_warning("RNDFLD", "Randomization failed in uvm_do") \
    end \
    finish_item(SEQ_OR_ITEM); \
  end

// Start item with inline constraints
`define uvm_do_with(SEQ_OR_ITEM, CONSTRAINTS) \
  begin \
    SEQ_OR_ITEM = new(`"SEQ_OR_ITEM`"); \
    start_item(SEQ_OR_ITEM); \
    if (!SEQ_OR_ITEM.randomize() with CONSTRAINTS) begin \
      `uvm_warning("RNDFLD", "Randomization failed in uvm_do_with") \
    end \
    finish_item(SEQ_OR_ITEM); \
  end

// Create sequence or item
`define uvm_create(SEQ_OR_ITEM) \
  SEQ_OR_ITEM = new(`"SEQ_OR_ITEM`")

// Send request and get response
`define uvm_send(SEQ_OR_ITEM) \
  begin \
    start_item(SEQ_OR_ITEM); \
    finish_item(SEQ_OR_ITEM); \
  end

// Start item on specified sequencer
`define uvm_do_on(SEQ_OR_ITEM, SEQR) \
  begin \
    SEQ_OR_ITEM = new(`"SEQ_OR_ITEM`"); \
    start_item(SEQ_OR_ITEM); \
    if (!SEQ_OR_ITEM.randomize()) begin \
      `uvm_warning("RNDFLD", "Randomization failed in uvm_do_on") \
    end \
    finish_item(SEQ_OR_ITEM); \
  end

`define uvm_do_on_with(SEQ_OR_ITEM, SEQR, CONSTRAINTS) \
  begin \
    SEQ_OR_ITEM = new(`"SEQ_OR_ITEM`"); \
    start_item(SEQ_OR_ITEM); \
    if (!SEQ_OR_ITEM.randomize() with CONSTRAINTS) begin \
      `uvm_warning("RNDFLD", "Randomization failed in uvm_do_on_with") \
    end \
    finish_item(SEQ_OR_ITEM); \
  end

// ============================================================================
// Analysis Port Macros
// ============================================================================

`define uvm_analysis_imp_decl(SFX) \
  class uvm_analysis_imp``SFX #(type T = int, type IMP = int) extends uvm_analysis_port #(T); \
    IMP m_imp; \
    function new(string name, IMP imp); \
      super.new(name, null); \
      m_imp = imp; \
    endfunction \
    virtual function void write(T t); \
      m_imp.write``SFX(t); \
    endfunction \
  endclass

// ============================================================================
// TLM Port Macros (simplified)
// ============================================================================

`define uvm_blocking_put_imp_decl(SFX)
`define uvm_nonblocking_put_imp_decl(SFX)
`define uvm_blocking_get_imp_decl(SFX)
`define uvm_nonblocking_get_imp_decl(SFX)

// ============================================================================
// Deprecated/Compatibility Macros
// ============================================================================

`define uvm_component_param_utils(T) \
  `uvm_component_utils(T)

`define uvm_object_param_utils(T) \
  `uvm_object_utils(T)

// ============================================================================
// Misc Utility Macros
// ============================================================================

// Declare sequence library (no-op in simplified implementation)
`define uvm_declare_p_sequencer(SEQUENCER)

// Random sequence selection (simplified)
`define uvm_rand_send(SEQ_OR_ITEM) \
  `uvm_do(SEQ_OR_ITEM)

`endif // UVM_MACROS_SVH
