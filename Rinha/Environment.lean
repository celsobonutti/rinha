import Std.Data.HashMap.Basic
import Rinha.Term

open Rinha.Term

namespace Rinha.Environment

def Environment := Std.HashMap String Term

def init : Environment := Std.HashMap.empty

end Rinha.Environment
