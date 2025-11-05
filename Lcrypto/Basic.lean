inductive Program (α : Type) where
| Pure : α → Program α
| Sample : (Bool → Program α) → Program α

def Program.map (f : α → β) (prog : Program α) : Program β := match prog with
  | Program.Pure a => Program.Pure (f a)
  | Program.Sample k => Program.Sample (fun s => map f (k s))

instance : Functor Program where
  map := Program.map
