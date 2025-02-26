# Descript
**This could be a final repo for descript.** The project has been refactored several times and 
this repo is considered as the last repository in maintenance.

Its name _Descript_ is created under the word _Description_. As its name shows, the language
is designed to better describe what you want to implement seamlessly through codes.


## Features

### Annotation-Free Parametric Polymorphism
```js
(x) => x
with<T>(x:T) T => x   /* Equivalent */

(a, (fst, snd)) => (a, fst, snd)
with<T, U, V>(a:T, (fst:U, snd:V)) (T, U, V) => (a, fst, snd)
```

### Scalable SubML
```js
let rcd1 = {a = 42, b = "Hello"};
let rcd2 = {a = 42, b = "Hello", c = true};
let rcd3 = {a = 42}

let f = (x) => (x.a, x.b);
// f :: ∀α, β, γ. (α) -> (β, γ) where α: {b: γ, a: β}~⊤; γ: ⊥~⊤; β: ⊥~⊤

f(rcd1) // Fine
f(rcd2) // Fine
f(rcd3) // Error!
```
