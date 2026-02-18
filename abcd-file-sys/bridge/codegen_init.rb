# Combined Gen.on_require for abcd-file-sys codegen.
# Each vendor .rb file redefines Gen.on_require, but we need all three
# data wrappers initialized for our templates.

def Gen.on_require(data)
  Panda.wrap_data(data)
  Common.wrap_data(data)
  PandaFile.wrap_data(data)
end
