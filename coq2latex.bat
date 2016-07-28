@echo off

((echo Set Printing Depth 2. Load GradVer0Defs. Set Printing All. Set Printing Width 2097151. Set Printing Depth 100. Print Semantics.sfrme. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer0Defs.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe Semantics.sfrme^
    > latex\staticExpression.tex

((echo Set Printing Depth 2. Load GradVer0Defs. Set Printing All. Set Printing Width 2097151. Set Printing Depth 100. Print Semantics.sfrmphi'. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer0Defs.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe Semantics.sfrmphi'^
    > latex\staticFormula.tex

((echo Set Printing Depth 2. Load GradVer0Defs. Set Printing All. Set Printing Width 2097151. Set Printing Depth 100. Print Semantics.hoare. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer0Defs.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe Semantics.hoare^
    > latex\staticSemantics.tex

((echo Set Printing Depth 2. Load GradVer0Defs. Set Printing All. Set Printing Width 2097151. Set Printing Depth 100. Print Semantics.evalphi'. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer0Defs.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe Semantics.evalphi'^
    > latex\dynamicFormula.tex

((echo Set Printing Depth 2. Load GradVer0Defs. Set Printing All. Set Printing Width 2097151. Set Printing Depth 100. Print Semantics.dynSem. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer0Defs.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe Semantics.dynSem^
    > latex\dynamicSemanticsX.tex

GOTO:EOF
