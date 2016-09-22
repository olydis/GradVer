@echo off

((echo Set Printing Depth 2. Load GradVer0Defs. Set Printing All. Set Printing Width 2097151. Set Printing Depth 100. Print Semantics.hasStaticType. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer0Defs.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe Semantics.hasStaticType^
    > ..\GradVerThesis\data\autogen\staticTypeExpression.tex

((echo Set Printing Depth 2. Load GradVer0Defs. Set Printing All. Set Printing Width 2097151. Set Printing Depth 100. Print Semantics.sfrme. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer0Defs.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe Semantics.sfrme^
    > ..\GradVerThesis\data\autogen\staticExpression.tex

((echo Set Printing Depth 2. Load GradVer0Defs. Set Printing All. Set Printing Width 2097151. Set Printing Depth 100. Print Semantics.sfrmphi'. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer0Defs.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe Semantics.sfrmphi'^
    > ..\GradVerThesis\data\autogen\staticFormula.tex

((echo Set Printing Depth 2. Load GradVer0Defs. Set Printing All. Set Printing Width 2097151. Set Printing Depth 100. Print Semantics.hoare. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer0Defs.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe Semantics.hoare^
    > ..\GradVerThesis\data\autogen\staticSemantics.tex

((echo Set Printing Depth 2. Load GradVer0Defs. Set Printing All. Set Printing Width 2097151. Set Printing Depth 100. Print Semantics.evalphi'. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer0Defs.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe Semantics.evalphi'^
    > ..\GradVerThesis\data\autogen\dynamicFormula.tex

((echo Set Printing Depth 2. Load GradVer0Defs. Set Printing All. Set Printing Width 2097151. Set Printing Depth 100. Print Semantics.dynSem. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer0Defs.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe Semantics.dynSem^
    > ..\GradVerThesis\data\autogen\dynamicSemantics.tex

((echo Set Printing Depth 2. Load GradVer0Defs. Set Printing All. Set Printing Width 2097151. Set Printing Depth 100. Print writesTo. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer0Defs.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe writesTo^
    > ..\GradVerThesis\data\autogen\writesTo.tex

GOTO:EOF
