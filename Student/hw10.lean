variable
  (Animal : Type)
  (Likes : Animal → Animal → Prop)


-- 1.
#check ∀ (dog : Animal), ∃ (cat : Animal), Likes dog cat

-- 2.
#check ∀ (d g w : Animal), Likes d g → Likes g w → Likes d w

-- 3.
#check ∀ (c d : Animal), (∃ (likedCat : Animal), Likes c likedCat) → Likes d c

-- 4.
#check ∀ (c : Animal), Likes c c

-- 5.
#check ∀ (c d : Animal), (∀ (cat : Animal), Likes c cat → Likes d cat → Likes c d)


example : ∀ (c d : Animal), (∀ (cat : Animal), Likes c cat →
 Likes d cat → Likes c d)
| ⟨ cat ,cat_love_cat c d⟩ =>
  fun (c d : Animal) =>
   ⟨ cat , cat_love_cat c d⟩
