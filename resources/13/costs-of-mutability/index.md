---
marp: true
---

# Costs of mutability
## (in dynamic programming languages)

<div style = "height: 2em;"></div>

Michal Vlasák, 2023

---

# What is mutability?


```js
let o = { 1: "one" };
Object.freeze(o);
console.log(o);     // { '1': 'one' }
o = { 2: "two" };
console.log(o);     // { '2': 'two' }
```

Frozen object, but can be modified?

---

# What is mutability?

```js
const a = [ 1, 2 ];
console.log(a);     // [ 1, 2 ]
a[0] = 3;
console.log(a);     // [ 3, 2 ]
```


Constant variable, but can be modified?

---

# Two kinds of mutability

* Mutability of values (e.g. frozen vs normal object)

* Mutability of binding (`let` vs `const`)

---

![bg right w:50%](figure/binding1.png)

```javascript
```

---

![bg right w:50%](figure/binding2.png)

```javascript
let a = 1;
```

---

![bg right w:50%](figure/binding3.png)

```javascript
let a = 1;
```

---

![bg right w:50%](figure/binding4.png)

```javascript
let a = 1;
let b = a;
```

---

![bg right w:50%](figure/binding5.png)

```javascript
let a = 1;
let b = a;
```

---

![bg right w:50%](figure/binding5.png)

```javascript
let a = 1;
let b = a;
a = a + 1;
```

---

![bg right w:50%](figure/binding6.png)

```javascript
let a = 1;
let b = a;
a = a + 1;
```

---

![bg right w:50%](figure/mutation1.png)

```js
let a = 1;
let b = a;
```

---

![bg right w:50%](figure/mutation2.png)

```js
let a = 1;
let b = a;
// mutate integer in place
a.increment();
```

---

![bg right w:50%](figure/mutation3.png)

```js
let a = 1;
let b = a;
// mutate integer in place
a.increment();
```

---

![bg right contain](figure/heap1.png)

```js
let a = 1;
let b = a;
// mutate integer in place
a.increment();
```

---

![bg right contain](figure/heap1.png)

```js
```

---

![bg right contain](figure/heap1.png)

```js
let a = 1;
```

---

![bg right contain](figure/heap2.png)

```js
let a = 1;
```

---

![bg right contain](figure/heap3.png)

```js
let a = 1;
```

---

![bg right contain](figure/heap3.png)

```js
let a = 1;
let b = a;
```

---

![bg right contain](figure/heap4.png)

```js
let a = 1;
let b = a;
```

---

![bg right contain](figure/heap4.png)

```js
let a = 1;
let b = a;
// mutate integer in place
a.increment();
```
---

![bg right contain](figure/heap5.png)

```js
let a = 1;
let b = a;
// mutate integer in place
a.increment();
```

---

![bg right contain](figure/shadow1.png)

```js
const a = 1;
```

---

![bg right contain](figure/shadow1.png)

```js
const a = 1;
{
        const a = 2;
}
```

---

![bg right contain](figure/shadow3.png)

```js
const a = 1;
{
        const a = 2;
}
```

---

Typically:

1) assignment to local variable is a mutation of _binding_,

2) other mutations are mutations of _values_.

      - including assignments to an object fields or array indeces.


---

# Value representation

* Dynamic programming language
  - *values* have types
  - (vs static programming languages where *expressions* have types)

* Value is represented by pointer to heap
  - extra level of indirection for mutability
  - pass by reference

* For immutable data pass-by-value can be used

---

```c++
struct EnvironmentEntry {
	std::string_view name;
        Value value;
};

using Value = *HeapValue;

struct HeapValue {
        HeapValueKind kind;
};

enum class HeapValueKind {
        Integer,
        Array,
};
```

---

```c++

struct Integer : public HeapValue {
        int value;
};

struct Array : public HeapValue {
        int size;
        Value *array;
};

```

---

```c++
struct Array : public HeapValue {
        int size;
        Value *array;
};

struct HeapValue {
        HeapValueKind kind;
        union {
                int integer;
                Array array;
        } u;
};

```

---

# Python integers

* immutable

* but heap allocated

* costly for commonly used integers

* common integers preallocated (-5 through 256) 

* demo

---

# Interning / hash consing

* allocate at most one of each possible value of a type
   - e.g. each integer at most once

* saves memory
* cheap comparison (comparison of pointers)

* great for commonly used or commonly compared values

* Cons cells - LISP

---

# Strings

* Strings immutable and interned
  - e.g. Lua or (sometimes) Python

* Mutable
  - e.g. Ruby
  - demo

---

```ruby
k = "key"

hash = { k => "value" }

k.upcase!

hash[k]
hash["key"]
```

* Compares based on equality of values, not equality of pointers ("identity")

* But not always: http://jafrog.com/2012/10/07/mutable-objects-as-hash-keys-in-ruby.html

---

# Immutable strings

* Mutable strings have to be copied by hash maps
* Expensive copy, expensive comparison

* Ruby has immutable strings: "symbols" (`:string`)
  * two string types - complicated

---

# Closures

```js
function make_counter(initial) {
	let value = initial;

	function inc() { value += 1; }
	function get() { return value; }

	return { inc: inc, get: get };
}
```

 * bindings become shared

 * shared *and* mutable?
   * need a level of indirection

---


![bg right w:50%](figure/closure5.png)

```js
function make_counter(initial) {





}
```

---


![bg right w:50%](figure/closure4.png)

```js
function make_counter(initial) {





}
```

---


![bg right w:100%](figure/closure3.png)

```js
function make_counter(initial) {
	let value = initial;




}
```

---


![bg right w:100%](figure/closure2.png)

```js
function make_counter(initial) {
	let value = initial;

	function inc() { value += 1; }



}
```

---


![bg right w:100%](figure/closure1.png)

```js
function make_counter(initial) {
	let value = initial;

	function inc() { value += 1; }
	function get() { return value; }


}
```

---


![bg right w:100%](figure/closure1.png)

```js
function make_counter(initial) {
	let value = initial;

	function inc() { value += 1; }
	function get() { return value; }

	return { inc: inc, get: get };
}
```

---


![bg right w:100%](figure/closure_const1.png)

```js
function make_counter(initial) {
	const value = initial;

	function inc() { value.increment(); }
	function get() { return value; }

	return { inc: inc, get: get };
}

```

---


![bg right w:100%](figure/closure_const2.png)

```js
function make_counter(initial) {
	const value = initial;

	function inc() { value.increment(); }
	function get() { return value; }

	return { inc: inc, get: get };
}
```

---

# Garbage collection

---

## Reference counting

* each object stores the number of references to itself

* object can be freed when counter reaches 0

---

![bg w:90%](figure/rc1.png)

---

![bg w:90%](figure/rc2.png)

---

![bg w:90%](figure/rc2.png)

---

![bg w:90%](figure/rc3.png)

---

![bg w:90%](figure/rc4.png)

---

![bg w:90%](figure/rc5.png)

---

![bg w:90%](figure/rc6.png)

---

![bg w:90%](figure/rc7.png)

---

![bg w:90%](figure/rc8.png)

---

![bg w:80%](figure/Spiderman-Pointing-Meme.webp)

---

* If objects are immutable, there is no way to create cycles!

* But interestingly the immutable objects suddenly became mutable, because we added the reference count!

---

## Tracing

* Mark all reachable (potentially useful) objects recursively
  - start from trivially reachable objects, like local variables

* No problem with cycles
  - mark bit prevents visiting live objects twice
  - dead objects are never even visited

* Allows easily for defragmentation

---

![bg w:90%](figure/marking0.png)

---

![bg w:90%](figure/marking1.png)

---

![bg w:90%](figure/marking2.png)

---

![bg w:90%](figure/marking3.png)

---

![bg w:90%](figure/marking4.png)

---

![bg w:90%](figure/marking5.png)

---

![bg w:90%](figure/marking6.png)

---

![bg w:90%](figure/marking7.png)

---

# Compaction

---

![bg w:90%](figure/sliding0.png)

---

![bg w:90%](figure/sliding1.png)

---

![bg w:90%](figure/sliding2.png)

---

![bg w:90%](figure/sliding3.png)

---

![bg w:90%](figure/sliding5.png)

---

![bg w:90%](figure/sliding7.png)

---

![bg w:90%](figure/sliding8.png)

---

![bg w:90%](figure/sliding9.png)

---

![bg w:90%](figure/sliding9-1.png)

---

![bg w:90%](figure/sliding9-2.png)

---

![bg w:90%](figure/sliding10.png)

---

![bg w:90%](figure/sliding10-0.png)

---

![bg w:90%](figure/sliding10-1.png)

---

![bg w:90%](figure/sliding10-2.png)

---

![bg w:90%](figure/sliding10-3.png)

---

![bg w:90%](figure/sliding10-4.png)

---

![bg w:90%](figure/sliding10.png)

---

![bg w:90%](figure/sliding11.png)

---

![bg w:90%](figure/sliding12.png)

---

![bg w:90%](figure/sliding13.png)

---

## Incremental / generational garbage collection

- Pointers from old objects to young objects fail our scheme

- Solutions:

  * Immutability - no old object can ever point to young object

  * Write barrier - check *all writes* for destroying invariants

* Mostly immutable values (e.g. Scheme)

 * with occasional writes, we can get away with expensive write barriers

 * map old space memory read-only

---

# Ultimate mutatation

Smalltalk's `become`:

 * `a become: b`

 * > all references to the object denoted by a before the call point refer to the object that was denoted by b, and vice versa

 * https://gbracha.blogspot.com/2009/07/miracle-of-become.html

 * Not as simple as:

    ```javascript
    var tmp = a;
    a = b;
    b = tmp;
    ```

---

![bg w:50%](figure/become.png)

---

![bg w:50%](figure/become1.png)

---

* Requires changing every pointer to those two objects.

* Crazy, complex...

* Why?

* There are some uses, but probably because it was easy.

---

![bg w:50%](figure/become2.png)

---

![bg w:50%](figure/become3.png)

---

# Takeaways

* Mutability of values / bindings has a big impact on a design and implementation of a programming language

* Immutability makes a lot of things simpler

  * mutability sometimes needs an extra level of indirection

* > Every (mutability) problem can be solved with another layer of indirection.
