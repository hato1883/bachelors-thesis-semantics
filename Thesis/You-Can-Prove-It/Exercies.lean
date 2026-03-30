inductive Person where
  -- left blank

def is_scrub (p : Person) : Bool := sorry
def tlc_members : Set Person := sorry
def can_get_love_from (p1 p2 : Person) := sorry

def no_scrubs : Prop :=
  \all p t, t \in tlc_members \and is_scrub p -> \not can_get_love_from t p
