open Grain_typed;
open Grain_utils;
open Mashtree;

type linked_program = {
  programs: list(mash_program),
  func_import_resolutions: Hashtbl.t(string, string),
  global_import_resolutions: Hashtbl.t(string, string),
  num_function_table_elements: int,
  signature: Cmi_format.cmi_infos,
};

let stack_size_zero = {
  stack_size_ptr: 0,
  stack_size_i32: 0,
  stack_size_i64: 0,
  stack_size_f32: 0,
  stack_size_f64: 0,
};
let max_stack_size = (s1, s2) => {
  {
    stack_size_ptr: max(s1.stack_size_ptr, s2.stack_size_ptr),
    stack_size_i32: max(s1.stack_size_i32, s2.stack_size_i32),
    stack_size_i64: max(s1.stack_size_i64, s2.stack_size_i64),
    stack_size_f32: max(s1.stack_size_f32, s2.stack_size_f32),
    stack_size_f64: max(s1.stack_size_f64, s2.stack_size_f64),
  };
};

let link = main_mashtree => {
  let main_module = Module_resolution.current_filename^();
  // prerr_endline(Module_resolution.locate_unit_object_file(main_module));
  let new_base_dir = Filepath.String.dirname;
  // let base_dir = Filepath.String.dirname(main_module);

  let resolve = (~base_dir=?, mod_name) =>
    Module_resolution.locate_unit_object_file(~base_dir?, mod_name);

  let dependencies = Module_resolution.get_dependencies();

  let func_import_resolutions = Hashtbl.create(2048);
  let global_import_resolutions = Hashtbl.create(2048);
  let func_export_resolutions = Hashtbl.create(2048);
  let global_export_resolutions = Hashtbl.create(2048);

  let num_function_table_elements = ref(0);

  let dep_id = ref(0);

  let process_mashtree = (~main, dep, tree) => {
    let table_offset_global = (
      tree.global_function_table_offset,
      false,
      Types.Unmanaged(WasmI32),
      Some(
        MConstLiteral(
          MConstI32(Int32.of_int(num_function_table_elements^)),
        ),
      ),
    );

    let globals = [table_offset_global, ...tree.globals];

    let imports =
      List.fold_left(
        (imports, import) => {
          switch (import.mimp_kind) {
          | MImportWasm => [import, ...imports]
          | MImportGrain =>
            let resolved_module =
              resolve(~base_dir=new_base_dir(dep), import.mimp_mod);

            let global =
              Hashtbl.find(
                global_export_resolutions,
                (resolved_module, import.mimp_name),
              );
            let func =
              Hashtbl.find_opt(
                func_export_resolutions,
                (resolved_module, import.mimp_name),
              );
            let import_name =
              Printf.sprintf(
                "%s_%d",
                Ident.unique_name(import.mimp_id),
                dep_id^,
              );
            Hashtbl.add(global_import_resolutions, import_name, global);
            Option.iter(
              func => Hashtbl.add(func_import_resolutions, import_name, func),
              func,
            );

            imports;
          }
        },
        [],
        tree.imports,
      );

    List.iter(
      export => {
        switch (export) {
        | WasmFunctionExport({ex_function_name, ex_function_internal_name}) =>
          let internal_name =
            Printf.sprintf("%s_%d", ex_function_internal_name, dep_id^);
          Hashtbl.add(
            func_export_resolutions,
            (dep, ex_function_name),
            internal_name,
          );
          // FIXME: this is honestly a bit of a hack
          switch (tree.compilation_mode) {
          | Config.Runtime =>
            Hashtbl.add(
              func_import_resolutions,
              Ident.unique_name(Ident.create_persistent(ex_function_name)),
              internal_name,
            )
          | Normal => ()
          };
        | WasmGlobalExport({ex_global_name, ex_global_internal_name}) =>
          let internal_name =
            Printf.sprintf("%s_%d", ex_global_internal_name, dep_id^);
          Hashtbl.add(
            global_export_resolutions,
            (dep, ex_global_name),
            internal_name,
          );
          switch (tree.compilation_mode) {
          | Config.Runtime =>
            Hashtbl.add(
              global_import_resolutions,
              Ident.unique_name(Ident.create_persistent(ex_global_name)),
              internal_name,
            )
          | Normal => ()
          };
        }
      },
      tree.exports,
    );

    let exports =
      if (main) {
        tree.exports;
      } else {
        [];
      };

    num_function_table_elements :=
      num_function_table_elements^ + List.length(tree.function_table_elements);

    incr(dep_id);

    {...tree, globals, imports, exports};
  };

  let programs =
    List.rev_map(
      dep => {
        let ic = open_in_bin(dep);
        assert(input_byte(ic) == 0xF0);
        assert(input_byte(ic) == 0x9F);
        assert(input_byte(ic) == 0x8C);
        assert(input_byte(ic) == 0xBE);
        let cmi_length = input_binary_int(ic);
        seek_in(ic, cmi_length + 8);
        let tree = input_value(ic);
        // let tree =
        //   Sexplib.Sexp.load_sexp_conv_exn(dep, Mashtree.mash_program_of_sexp);

        process_mashtree(~main=false, dep, tree);
      },
      dependencies,
    );

  let main_program = process_mashtree(~main=true, main_module, main_mashtree);
  let programs = List.rev([main_program, ...programs]);
  let num_function_table_elements = num_function_table_elements^;
  let signature = main_mashtree.signature;

  {
    programs,
    func_import_resolutions,
    global_import_resolutions,
    num_function_table_elements,
    signature,
  };
};
