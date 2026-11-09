import PathMapModel.Source
import PathMapModel.Sources.Tracker
import PathMapModel.Sources.Overlay
import PathMapModel.Sources.Diff

/-!
# The source registry

Every read source, by the name `pathmap-oracle --source NAME` takes.  The list
must match `SOURCES` in `differential/src/sources/mod.rs`.
-/

namespace PathMapModel

def Source.all : List Source :=
  [ Source.native, Source.act, Source.tracker, Source.overlay, Source.overlayFilter, Source.diff ]

def Source.byName (n : String) : Option Source :=
  Source.all.find? (·.name == n)

end PathMapModel
