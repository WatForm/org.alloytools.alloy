# Portus Architecture

The architecture is based around the `Translator` interface. A Translator is something
that can attempt to translate an Alloy `Expr` into a Fortress `Term`. It is possible for
a Translator to fail to translate an expression; in that case, it returns `null`. A
Translator encapsulates all the translation logic for a particular optimization in one
place.

Translators take a `TranslationContext` parameter, which is a mutable class representing
the context of the translation. This includes the Fortress `Theory` being built up
(encapsulated inside the `TranslationContext` through methods delegating to it), as well
as the `ScopeComputer` and other metadata and useful information about the translation.
Translators must not mutate the passed `TranslationContext` if they fail to translate
the expression they are given (i.e. if they return `null`), but they may mutate it
if they successfully translate the expression (for example, to add a new function to
the theory).

The entry point to the translation process is the `TranslateAlloyToFortress` class.
It simply delegates to the `TranslatorManager` class for each translation, which uses the
`PortusOptions` (representing user-configured options) to come up with a list of
translators. When asked to translate an expression, `TranslatorManager` delegates to
each of the translators in the list in turn until one successfully translates the
expression, or throws an exception if none of them can.

All other translators are subclasses of `AbstractTranslator`, which provides a base
`Translator` implementation. This base class provides convenience overloads so subclasses
can only provide translations for the types of expressions they're interested in, as
well as a `recursivelyTranslate` method, which delegates to a "top-level" `Translator` which
is passed into the class. In normal execution, this is the `TranslatorManager`, and
subclasses should use `recursivelyTranslate` when recursively translating subexpressions
so that `TranslatorManager` can give other translators a chance to translate the
expression. In unit tests, the top-level translator can be replaced with a mock translator
so we can test only the translation of the current expression without its subexpressions.

`DefaultTranslator` provides the unoptimized translations for every supported Alloy
expression. All other translators provide particular optimizations.

Some pseudo-UML of the architecture:
```text
<<interface>>
  Translator
+ translate(Expr, TranslationContext)
    / \
     |------------------------------------------------------
     |                                                      |
TranslatorManager<------TranslateAlloyToFortress    AbstractTranslator
      |                                                    / \
      v                                                     |
FortressOptions                                     --------|--------
                                                   |                 |
                                           DefaultTranslator        ...
```
