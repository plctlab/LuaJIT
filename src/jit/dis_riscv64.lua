local dis_riscv = require((string.match(..., ".*%.") or "").."dis_riscv")
return {
  create = dis_riscv.create,
  disass = dis_riscv.disass,
  regname = dis_riscv.regname
}