import PathMapModel.Source
import PathMapModel.Sources.Tracker
import PathMapModel.Sources.Overlay
import PathMapModel.Sources.Diff
import PathMapModel.Sources.Dependent
import PathMapModel.Sources.Head
import PathMapModel.Sources.Owned
import PathMapModel.Sources.Empty
import PathMapModel.Sources.Prefix

/-!
# The source registry

Every read source, by the name `pathmap-oracle --source NAME` takes.  The list
must match `SOURCES` in `differential/src/sources/mod.rs`.
-/

namespace PathMapModel

def Source.all : List Source :=
  [ Source.native, Source.act, Source.tracker, Source.overlay, Source.overlayFilter, Source.diff,
    Source.dependent, Source.dependentLazy, Source.head, Source.owned, Source.empty ]
  [ Source.native, Source.act, Source.tracker, Source.empty, Source.prefix ]

def Source.byName (n : String) : Option Source :=
  Source.all.find? (·.name == n)

end PathMapModel
