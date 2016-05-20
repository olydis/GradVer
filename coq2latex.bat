@echo off

((echo Set Printing All. Set Printing Width 2097151. Load GradVer. Print Semantics.hoareSingle. Quit.^
    | C:\Users\Johannes\AppData\Roaming\Coq\bin\coqtop.exe) && type GradVer.v)^
    | ..\coq2latex\project\coq2latex\bin\Debug\coq2latex.exe hoareSingle