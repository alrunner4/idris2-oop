module OOP.VisitorPattern
import Control.Monad.Identity {- runIdentity -}

||| This dependent pair type enables something like a C++ dynamic_cast via case.
||| The ways that `d` can constrain `t` are more varied in Idris than C++, where our `d` takes the
|||    place of a base class. Algebraic and dependent types give `d` in Idris the opportunity for
|||    additional specificity.
public export
Dynamic: (Type -> Type) -> Type
Dynamic d = (t:Type ** d t)

||| You could just write `(_ ** x)` to introduce a `Dynamic` value, but `dynamic x` reads better.
public export
dynamic: {t: Type} -> d t -> Dynamic d
dynamic dt = (t ** dt)

||| I'm using the term "accept" here in the sense that it's used in the OOP Visitor pattern. In the
|||    conventional terminology, a "visitable" object implements "accept(visitor)" by calling a
|||    method on the visiting object corresponding to the visited type.
||| `DynamicAcceptor d pointer` is the type of functions that can use a `pointer` to dispatch an
|||    operation with `Dynamic d` input. `Applicative` and `Monoid` constraints help us ensure that
|||    these visitor operations can be composed over data structures in an expected manner.
||| An implemented function with type `DynamicAcceptor d pointer` should enable the caller to
|||    "visit" every part of the `pointer` object from which we can project a `Dynamic d`.
public export
0 DynamicAcceptor: (Type -> Type) -> Type -> Type
DynamicAcceptor d pointer =
   {0 f: Type -> Type} -> {auto Applicative: Applicative f} ->
   {0 a: Type} -> {auto Monoid: Monoid a} ->
   pointer -> (Dynamic d -> f a) -> f a

public export
ExtendWith: (Type -> Type) -> (Type -> Type) -> Type
ExtendWith d ex = Dynamic$ \t => let dt = d t in (dt, ex dt)

public export
extendWith: (ex: Type -> Type) ->
   {d: Type -> Type} -> {t: Type} -> {auto extension: ex (d t)} -> d t ->
   ExtendWith d ex
extendWith ex dt = dynamic (dt, extension)

||| A `Dynamic` value can be made `Visitable` by pairing it with a `DynamicAcceptor`.
public export
0 Visitable: (Type -> Type) -> Type
Visitable d = d `ExtendWith` DynamicAcceptor d

||| `DynamicVisit` provides a name for visitable types to implement their canonical visitation
|||    traversal acceptor.
public export
interface DynamicVisit d pointer where
   (.visit): DynamicAcceptor d pointer

public export
DynamicVisit d (Visitable d) where
   (.visit) (_ ** (details, visit)) visitor = visit details visitor

-- The following implementation is less useful than it might seem; if we can implement this, why do
--    we need `Visitable`? `Visitable` allows us to add a traversal algorithm as the
--    `DynamicAcceptor` where this implementation simply applies a single dynamic value to a dynamic
--    `Applicative` operation. The implementation of `DynamicVisit (Dynamic d) d` is omitted here to
--    discourage confusion between the use of `Dynamic` and `Visitable`.
-- public export
-- DynamicVisit (Dynamic d) d where
--    (.visit) source visitor = visitor source

||| A convenience function for accumulating the result of a pure visitor.
public export
(.concat): DynamicVisit d pointer =>
   {a: Type} -> {auto Monoid: Monoid a} ->
   pointer -> (Dynamic d -> a) -> a
(.concat) source visitor = runIdentity( source.visit (pure . visitor) )

||| A convenience function to use the `DynamicVisit` interface to produce a `Visitable`.
public export
visitable: {t: Type} -> DynamicVisit d (d t) => d t -> Visitable d
visitable x = ( t ** (x, (.visit)) )

||| Removes visitability by dropping the `DynamicAcceptor`, exposing the underlying `Dynamic`.
public export
unvisitable: Visitable d -> Dynamic d
unvisitable( _ ** (x, _) ) = (_ ** x)
