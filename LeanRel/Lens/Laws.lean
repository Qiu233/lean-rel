/-! Algebraic lens laws, separate from the checked partial relational implementation. -/
namespace LeanRel.Lens

structure Lens (Source View : Type) where
  get : Source → View
  put : Source → View → Source

structure Lawful (lens : Lens S V) : Prop where
  getPut : ∀ source, lens.put source (lens.get source) = source
  putGet : ∀ source view, lens.get (lens.put source view) = view

def Lens.id : Lens S S := ⟨fun s => s, fun _ v => v⟩
def Lens.comp (first : Lens S V) (second : Lens V W) : Lens S W :=
  ⟨second.get ∘ first.get, fun s w => first.put s (second.put (first.get s) w)⟩

theorem lawful_id : Lawful (Lens.id (S := S)) := ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem lawful_comp (a : Lens S V) (b : Lens V W) (ha : Lawful a) (hb : Lawful b) :
    Lawful (a.comp b) where
  getPut s := by
    change a.put s (b.put (a.get s) (b.get (a.get s))) = s
    rw [hb.getPut, ha.getPut]
  putGet s w := by
    change b.get (a.get (a.put s (b.put (a.get s) w))) = w
    rw [ha.putGet, hb.putGet]

end LeanRel.Lens
