import FreeFoil.Annotated
import FreeFoil.NbE.Fragment

namespace FreeFoil.NbE

/-- Run a fragment on syntax with transparent annotations. Annotation wrappers
demand only their subject. The fragment builds semantic nodes with the original
operators, which represent blank annotations. Full readback also blanks the
annotations under binders, while weak-head readback preserves wrappers in frozen
bodies. Languages whose evaluation uses annotation terms can supply their own
`Rules` on the annotated signature. -/
def Fragment.annotated {sig : Signature} (fragment : Fragment sig) (metadata : Type) :
    Fragment (sig.annotated metadata) :=
  let original : sig.Embedding (sig.annotated metadata) :=
    ⟨.original, fun _ => rfl, fun _ => rfl⟩
  {
    reduce position evaluator op := match op with
      | .original op => fragment.reduce (original.trans position) evaluator op
      | .annotation _ _ => fun terms _ => some <$> evaluator.force (terms 0)
    isHead op := match op with
      | .original op => fragment.isHead op
      | .annotation _ _ => fun _ => false
    eta position op := match op with
      | .original op => by
        simpa [Signature.Embedding.trans, original] using fragment.eta (original.trans position) op
      | .annotation _ _ => none
  }

end FreeFoil.NbE
