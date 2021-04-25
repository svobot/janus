let 0 proj1 = (\a b p. let _ @ x,_ = p in x : a)
            : (0 a : U) -> (0 b : (0 _ : a) -> U) -> (0 p : (0 x : a) * b x) -> a

let 0 proj2 = (\a b p. let z @ _,y = p in y : b (proj1 a b z))
            : (0 a : U) -> (0 b : (0 _ : a) -> U) -> (0 p : (0 x : a) * b x) -> b (proj1 a b p)

let 0 ofcW = (λa. (w _ : a) * I) : (0 _ : U) -> U
let w ofcElim = λa b exp f. let z @ x,y = exp in
                              (let _ @ () = y in f x : b exp)
                            : b exp
              : ∀ (0 a : U)
                  (0 b : (0 _ : ofcW a) -> U)
                  (1 exp : ofcW a)
                  (w f : (w x : a) -> b exp)
                . b exp


