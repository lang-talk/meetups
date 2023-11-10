---
# Preview with
#
#     nix run nixpkgs#nodePackages_latest.reveal-md -- index.md
#
# Compile to static site (in this directory) with:
#
#     nix run nixpkgs#nodePackages_latest.reveal-md -- index.md --static .
#
title: Expression problem
theme: black
highlightTheme: monokai
revealOptions:
  transition: slide
  hash: true
  controls: false
  progress: false
  slideNumber: true
  #margin: -0.2
---

# Expression problem

Michal Vlasák, 2023

---

> The Expression Problem is a new name for an old problem.

- [Philip Wadler, 1998](https://homepages.inf.ed.ac.uk/wadler/papers/expression/expression.txt)

---


The goal is to:

 - define a datatype by cases, where <!-- .element: class="fragment" data-fragment-index="1" -->
 - where one can add new cases to the datatype and <!-- .element: class="fragment" data-fragment-index="2" -->
 - new functions over the datatype. <!-- .element: class="fragment" data-fragment-index="3" -->

---

 <table border=1>
      <tr>
        <th>Expression</th>
        <th>Evaluate</th>
        <th>To String</th>
        <th>...</th>
      </tr>
      <tr>
        <th>Add</th>
        <td>✓</td>
        <td>✓</td>
        <td></td>
      </tr>
      <tr>
        <th>Multiply</th>
        <td>✓</td>
        <td>✓</td>
        <td></td>
      </tr>
      <tr>
        <th>Literal</th>
        <td>✓</td>
        <td>✓</td>
        <td></td>
      </tr>
      <tr>
        <th>...</th>
        <td></td>
        <td></td>
        <td></td>
      </tr>
    </table>

Note: Další operace: obsahuje nulu, zjednoduš, vyprinti jako LaTeX, ...

---

Objektový přístup

```cpp [55-61|3-5|10-18|25-32|39-47|7|20-22|34-36|49-51|-]
#include <iostream>

class Expr {
public:
	virtual int eval() = 0;

	virtual std::string to_str() = 0;
};

class Add : public Expr {
	Expr *left, *right;
public:
	Add(Expr *left, Expr *right)
        : left(left), right(right) {}

	virtual int eval() {
        return left->eval() + right->eval();
    }

	virtual std::string to_str() {
        return left->to_str() + " + " + right->to_str();
    }
};

class Lit : public Expr {
	int num;
public:
	Lit(int num) : num(num) {}

	virtual int eval() {
        return num;
    }

	virtual std::string to_str() {
        return std::to_string(num);
    }
};

class Mul : public Expr {
	Expr *left, *right;
public:
	Mul(Expr *left, Expr *right)
        : left(left), right(right) {}

	virtual int eval() {
        return left->eval() * right->eval();
    }

	virtual std::string to_str() {
        return left->to_str() + " * " + right->to_str();
    }
};

int main() {
	Expr *expr = new Add(
        new Lit(1),
        new Mul(new Lit(2), new Lit(3))
    );

	std::cout << expr->to_str() << " = " << expr->eval()
        << std::endl;
}
```

---

Funkcionální přístup

```rust [1-3|8-12|18-23|4|13-14|24-26|-]
enum Expr {
    Add { left: Box<Expr>, right: Box<Expr> },
    Lit { num: i32 },
    Mul { left: Box<Expr>, right: Box<Expr> },
}

impl Expr {
    fn eval(&self) -> i32 {
        match self {
            Expr::Add { left, right }
                => left.eval() + right.eval(),
            Expr::Lit { num } => *num,
            Expr::Mul { left, right }
                => left.eval() * right.eval(),
        }
    }

    fn to_str(&self) -> String {
        match self {
            Expr::Add { left, right } =>
                format!("{} + {}",
                    left.to_str(), right.to_str()),
            Expr::Lit { num } => num.to_string(),
            Expr::Mul { left, right } =>
                format!("{} * {}",
                    left.to_str(), right.to_str()),
        }
    }
}

fn main() {
    let expr = Box::new(Expr::Add {
        left: Box::new(Expr::Lit { num: 1 }),
        right: Box::new(Expr::Mul {
            left: Box::new(Expr::Lit { num: 2 }),
            right: Box::new(Expr::Lit { num: 3 }),
        }),
    });
    println!("{} = {}", expr2.to_str(), expr2.eval());
}
```

---

### Smůla

- Ani jeden přístup neřeší expression problem.

- Oba přístupy jsou si naprosto duální.

  - objektový přístup dovoluje lehko přidat nové varianty a těžko nové metody.

  - funkcionální přístup dovolouje lehko přidávat nové metody a těžko nové varianty.

---

### Co s tím?

 <table>
      <tr>
        <th>Expression</th>
        <th><code>eval</code></th>
        <th><code>to_string</code></th>
        <th>...</th>
      </tr>
      <tr>
        <th>Add</th>
        <td><code>eval_add</code></td>
        <td><code>to_string_add</code></td>
        <td></td>
      </tr>
      <tr>
        <th>Multiply</th>
        <td><code>eval_mul</code></td>
        <td><code>to_string_mul</code></td>
        <td></td>
      </tr>
      <tr>
        <th>Literal</th>
        <td><code>eval_lit</code></td>
        <td><code>to_string_lit</code></td>
        <td></td>
      </tr>
      <tr>
        <th>...</th>
        <td></td>
        <td></td>
        <td></td>
      </tr>
    </table>

Note: Co s tím? Potřebuju nějak nezávisle přidávat varianty. Algebraické datové typy určitě nejsou možnost, protože tam zafixuju počet variant už u definice datového typu. Takže to bude chtít nezávislé struktury a nezávislé funkce, pro každou možnost v matici. Zkusíme něco vymyslet v Céčku, kde bude vidět podstat problému.

---


```c [28-30|26|32-35|37-46|48-54|56-63|65-72|89-95|74-87|15-19|21-24|-]
#define _GNU_SOURCE
#include <stdio.h>
#include <stdarg.h>
char *fmt(char *fmt, ...) {
	va_list ap;
	va_start(ap, fmt);
	char *buf;
	vasprintf(&buf, fmt, ap);
	va_end(ap);
	return buf;
}

typedef struct Expr Expr;

typedef enum {
	ADD,
	MUL,
	LIT,
} ExprKind;

typedef struct {
	int (*eval)(Expr *e);
	char *(*to_str)(Expr *e);
} ExprVtable;

struct Expr { ExprKind kind; ExprVtable *vtable; };

typedef struct { Expr base; Expr *left; Expr *right; } Add;
typedef struct { Expr base; Expr *left; Expr *right; } Mul;
typedef struct { Expr base; int num; } Lit;

int eval(Expr *e);
int eval_add(Add *e) { return eval(e->left) + eval(e->right); }
int eval_mul(Mul *e) { return eval(e->left) * eval(e->right); }
int eval_lit(Lit *e) { return e->num; }

char *to_str(Expr *e);
char *to_str_add(Add *e) {
	return fmt("%s + %s", to_str(e->left), to_str(e->right));
}
char *to_str_mul(Mul *e) {
	return fmt("%s + %s", to_str(e->left), to_str(e->right));
}
char *to_str_lit(Lit *e) {
	return fmt("%d", e->num);
}

int eval_(Expr *e) {
	switch (e->kind) {
	case ADD: return eval_add((Add *) e);
	case MUL: return eval_mul((Mul *) e);
	case LIT: return eval_lit((Lit *) e);
	}
}

int eval1(Expr *e) {
	static int (*table[])(Expr *e) = {
		[ADD] = eval_add,
		[MUL] = eval_mul,
		[LIT] = eval_lit,
	};
	return table[e->kind](e);
}

char *to_str1(Expr *e) {
	static char *(*table[])(Expr *e) = {
		[ADD] = eval_add,
		[MUL] = eval_mul,
		[LIT] = eval_lit,
	};
	return table[e->kind](e);
}

static ExprVtable add_vtable = {
	.eval   = eval_add,
	.to_str = to_str_add,
};

static ExprVtable mul_vtable = {
	.eval   = eval_mul,
	.to_str = to_str_mul,
};

static ExprVtable lit_vtable = {
	.eval   = eval_lit,
	.to_str = to_str_lit,
};

int eval2(Expr *e) {
	return e->vtable->eval(e);
}

char *to_str2(Expr *e) {
	return e->vtable->to_str(e);
}
```

Note:

Úplně nezávislé varianty

Kvůli rozlišení dědí ze společné struktury, kde je buď diskriminátor nebo ukazatel na virtuální tabulku

Implementace jsou definované úplně nezávisle

Ve funkcionálním přístupu nám v rozšiřitelnosti o další typy vadí to, že nemůžeme nijak přidat další variantu do switche.

Takový switch se často přeloží na jump tabulku, kterou si můžeme nasimulovat

Máme jednu jump tabulku na každou implementovanou metodu, problém je přidání nových položek do jump tabulek

Při funkcionálním pojetí použijeme virtuální tabulky, kde je položka pro každou metodu, tzn. máme 3 tabulky po dvou metodách. V přidávání nových metod nám vadí to, že bychom museli přidat položky do všech virtuálních tabulek

Nezáleží jak organizuji kód, ale tabulky

---

## Řešení?

 - Dovolit přidávání nových variant do existujících metod.

 - Dovolit přidávání nových metod do existujících tříd (Monkey-patching).

 - Nezávislé přidávání metod a funkcí (multimetody).

Note:
Rozšíření FP

Rozšíření OOP

Principiálně dvojdimenzionální přístup

---

## Monkey-patching

Ruby, Python, JavaScript

```ruby [1|3-14|16-26|28-38|40-53|-]
class Expr end

class Add < Expr
  def initialize(left, right)
    @left = left
    @right = right
  end
end

class Lit < Expr
  def initialize(num)
    @num = num
  end
end

class Add
  def eval()
    @left.eval() + @right.eval()
  end
end

class Lit
  def eval()
    @num
  end
end

class Add
  def to_str()
    "#{@left.to_str()} + #{@right.to_str()}"
  end
end

class Lit
  def to_str()
    "#{@num}"
  end
end

class Mul < Expr
  def initialize(left, right)
    @left = left
    @right = right
  end

  def eval()
    @left.eval() * @right.eval()
  end

  def to_str()
    "#{@left.to_str()} * #{@right.to_str()}"
  end
end

expr = Add.new(Lit.new(1), Add.new(Lit.new(2), Lit.new(3)))
puts "#{expr.to_str()} = #{expr.eval()}"
```

Note: Problémy s kolizemi (můj a cizí balíček)

---

## Multimethods

Julia, Common Lisp (CLOS), Clojure

```julia [1|3-4|6-12|14-20|22-30|-]
abstract type Expr end

struct Add <: Expr; left::Expr; right::Expr; end
struct Lit <: Expr; num::Int32; end

function eval(expr::Add)::Int32
	eval(expr.left) + eval(expr.right)
end

function eval(expr::Lit)::Int32
	expr.num
end

function to_str(expr::Add)::String
	string(to_str(expr.left), " + ", to_str(expr.right))
end

function to_str(expr::Lit)::String
	string(expr.num)
end

struct Mul <: Expr; left::Expr; right::Expr; end

function eval(expr::Mul)::Int32
	eval(expr.left) * eval(expr.right)
end

function to_str(expr::Mul)::String
	string(to_str(expr.left), " * ", to_str(expr.right))
end

expr = Add(Lit(1), Add(Lit(2), Lit(3)))
print(string(to_str(expr), " = ", eval(expr), "\n"))
```

Note: Multiple dispatch

---

## Aspekty problému

 - "without recompiling existing code" <!-- .element: class="fragment" data-fragment-index="1" -->
 - "retaining static type safety (e.g., no casts)" <!-- .element: class="fragment" data-fragment-index="2" -->

 - rozšíření za běhu <!-- .element: class="fragment" data-fragment-index="3" -->
 - organizace kódu  <!-- .element: class="fragment" data-fragment-index="4" -->
 - složitost řešení  <!-- .element: class="fragment" data-fragment-index="5" -->
 - náročnost za běhu  <!-- .element: class="fragment" data-fragment-index="6" -->

---

##  Neřešit?

- Často stačí rozšiřitelnost na jedné ose.

- Využijeme standardní prostředky dostupných jazyků.

- Efektivní, přímočaré.

---

### OOP -> "FP"

```cpp
#include <iostream>

class Expr;
class Add;
class Lit;
class Mul;

class ExprVisitor {
public:
	virtual void visitAdd(Add *) = 0;
	virtual void visitMul(Mul *) = 0;
	virtual void visitLit(Lit *) = 0;
	virtual ~ExprVisitor() = default;
};

class Expr {
public:
	virtual void accept(ExprVisitor *) = 0;
};

class Add : public Expr {
public:
	Expr *left, *right;
	Add(Expr *left, Expr *right) : left(left), right(right) {}
	virtual void accept(ExprVisitor *visitor) {
        visitor->visitAdd(this);
    }
};

class Lit : public Expr {
public:
	int num;
	Lit(int num) : num(num) {}
	virtual void accept(ExprVisitor *visitor) {
        visitor->visitLit(this);
    }
};

class Mul : public Expr {
public:
	Expr *left, *right;
	Mul(Expr *left, Expr *right) : left(left), right(right) {}
	virtual void accept(ExprVisitor *visitor) {
        visitor->visitMul(this);
    }
};

class Evaluator : public ExprVisitor {
public:
	int res;
	int eval(Expr *e) { e->accept(this); return res; }
	virtual void visitAdd(Add *e) {
        res = eval(e->left) + eval(e->right);
    }
	virtual void visitMul(Mul *e) {
        res = eval(e->left) * eval(e->right);
    }
	virtual void visitLit(Lit *e) {
        res = e->num;
    }
};

class Stringifier : public ExprVisitor {
public:
	std::string res;
	std::string to_str(Expr *e) {
        e->accept(this); return res;
    }
	virtual void visitAdd(Add *e) {
        res = to_str(e->left) + " + " + to_str(e->right);
    }
	virtual void visitMul(Mul *e) {
        res = to_str(e->left) + " * " + to_str(e->right);
    }
	virtual void visitLit(Lit *e) {
        res = std::to_string(e->num);
    }
};

int main() {
	Evaluator E;
	Stringifier S;
	Expr *expr = new Add(
        new Lit(1),
        new Mul(new Lit(2), new Lit(3)),
    );
	std::cout << S.to_str(expr) << " = " << E.eval(expr)
        << std::endl;
}
```

---

Rust "OOP"

```rust
trait Expr {
    fn eval(&self) -> i32;
    fn to_str(&self) -> String;
}

struct Add {
    left: Box<dyn Expr>,
    right: Box<dyn Expr>,
}

impl Expr for Add {
    fn eval(&self) -> i32 {
        self.left.eval() + self.right.eval()
    }
    fn to_str(&self) -> String {
        format!("{} + {}", self.left.to_str(), self.right.to_str())
    }
}

struct Mul {
    left: Box<dyn Expr>,
    right: Box<dyn Expr>,
}

impl Expr for Mul {
    fn eval(&self) -> i32 {
        self.left.eval() * self.right.eval()
    }
    fn to_str(&self) -> String {
        format!("{} * {}", self.left.to_str(), self.right.to_str())
    }
}

struct Lit {
    num: i32,
}

impl Expr for Lit {
    fn eval(&self) -> i32 {
        self.num
    }
    fn to_str(&self) -> String {
        self.num.to_string()
    }
}

fn main() {
    let expr = Box::new(Add {
        left: Box::new(Lit { num: 1 }),
        right: Box::new(Mul {
            left: Box::new(Lit { num: 2 }),
            right: Box::new(Lit { num: 3 }),
        }),
    });
    println!("{} = {}", expr.to_str(), expr.eval());
}
```

---

### Další možnosti:

- C++, [std::visit](https://en.cppreference.com/w/cpp/utility/variant/visit)
- Java, [Pattern Matching for switch](https://openjdk.org/jeps/441)
- C++, "LLVM RTTI", [1](https://stackoverflow.com/a/5138926), [2](https://llvm.org/docs/ProgrammersManual.html#isa), [3](https://llvm.org/docs/HowToSetUpLLVMStyleRTTI.html)

---

### Moje zkušenost

- Překladače, interprety:
  - fixní varianty (AST, bajtkód)
  - stále nové operace (`print`, `verify`, `optimize`, `eval`, `serialize`, ...)
  - užitečný pattern matching
  - ne náhodou silná doména funkcionálních jazyků

Dynamic cast není nutně špatně, možná se jen potřebujete zamyslet nad expression problémem.

---

### Užitečné odkazy I

 - https://homepages.inf.ed.ac.uk/wadler/papers/expression/expression.txt
 - https://en.wikipedia.org/wiki/Expression_problem
 - https://wiki.c2.com/?ExpressionProblem
 - https://eli.thegreenplace.net/2016/the-expression-problem-and-its-solutions/
 - https://eli.thegreenplace.net/2018/more-thoughts-on-the-expression-problem-in-haskell/

---

### Užitečné odkazy II

 - https://www.youtube.com/watch?v=kc9HwsxE1OY
 - https://en.wikipedia.org/wiki/Monkey_patch
 - https://journal.stuffwithstuff.com/2010/10/01/solving-the-expression-problem/
 - https://journal.stuffwithstuff.com/2012/06/12/multimethods-global-scope-and-monkey-patching/
