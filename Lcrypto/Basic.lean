inductive Program (R : Type) (α : Type) where
| Pure : α → Program R α
| Sample : (R → Program R α) → Program R α
| Eq : R → R → (Bool → Program R α) → Program R α

def eval : (∀ R, Program R α) → α :=
  let rec inner (s : Nat) (p : Program Nat α) : α := match p with
    | Program.Pure a => a
    | Program.Sample φ => inner (s.succ) (φ s)
    | Program.Eq r1 r2 φ => inner s (φ (r1 == r2))
  fun p => inner 0 (p Nat)

namespace Program

variable {R : Type}

def sample : Program R R := Program.Sample Program.Pure

def eq (x : R) (y : R) : Program R Bool := Program.Eq x y Program.Pure

instance : Functor (Program R) where
  map :=
    let rec inner {α β} (f : α → β) (p : Program R α) : Program R β := match p with
      | Program.Pure a => Program.Pure (f a)
      | Program.Sample φ => Program.Sample (fun r => inner f (φ r))
      | Program.Eq r1 r2 φ => Program.Eq r1 r2 (fun b => inner f (φ b))
    inner

instance monad : Monad (Program R) where
  pure := Program.Pure
  bind :=
    let rec inner {α β} (p : Program R α) (f : α → Program R β) : Program R β := match p with
      | Program.Pure a => f a
      | Program.Sample φ => Program.Sample (fun r => inner (φ r) f)
      | Program.Eq r1 r2 φ => Program.Eq r1 r2 (fun b => inner (φ b) f)
    inner

def foo : Program R Bool := do
  let r <- sample
  eq r r

def foo_test : eval @foo = true := by
  rw [eval]
  rw [eval.inner.eq_def]
  rw [foo]
  rw [bind]
  rw [sample]
  rw [monad]
  simp
  rw [monad.inner]
  simp
  rw [monad.inner]
  rw [eq]
  rw [eval.inner.eq_def]
  simp
  rw [eval.inner.eq_def]

end Program
