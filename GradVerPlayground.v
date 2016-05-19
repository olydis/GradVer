
Open Scope string.
Definition C1 : C := "Class1".
Definition f1 : f := "f1".
Definition f2 : f := "f2".
Definition m1 : m := "m1".
Definition m2 : m := "m2".
Definition field1 : field := Field (TClass C1) f1.
Definition field2 : field := Field TPrimitiveInt f2.
Definition arg1 : x' := "arg1".
Definition contract1 : contract := Contract [phiTrue] [phiTrue].
Definition method1 : method := Method TPrimitiveInt m1 TPrimitiveInt arg1 contract1
  [
  ].
Definition arg2 : x' := "arg2".
Definition contract2 : contract := Contract [phiTrue] [phiTrue].
Definition method2 : method := Method TPrimitiveInt m2 TPrimitiveInt arg2 contract2
  [
  ].
Definition c1 : cls := Cls C1 [field1 ; field2] [method1 ; method2].
Definition p : program := Program [c1]
  [
  ].

Print Semantics.hoareSingle.
