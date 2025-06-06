
{-# LINE 1 "src/C2_NameLiterals.hs" #-}
module C2_NameLiterals where

import B_Base
import C1_Name

{-# noinline litN0 #-}
litN0 = fromStr "\""#
pattern N0 <- (eqName litN0 -> True)
  where N0 = fromName litN0

{-# noinline litN1 #-}
litN1 = fromStr "\n"#
pattern N1 <- (eqName litN1 -> True)
  where N1 = fromName litN1

{-# noinline litN2 #-}
litN2 = fromStr "--"#
pattern N2 <- (eqName litN2 -> True)
  where N2 = fromName litN2

{-# noinline litN3 #-}
litN3 = fromStr "SEMI"#
pattern N3 <- (eqName litN3 -> True)
  where N3 = fromName litN3

{-# noinline litN4 #-}
litN4 = fromStr "\t"#
pattern N4 <- (eqName litN4 -> True)
  where N4 = fromName litN4

{-# noinline litN5 #-}
litN5 = fromStr "\r"#
pattern N5 <- (eqName litN5 -> True)
  where N5 = fromName litN5

{-# noinline litN6 #-}
litN6 = fromStr "{-"#
pattern N6 <- (eqName litN6 -> True)
  where N6 = fromName litN6

{-# noinline litN7 #-}
litN7 = fromStr "-}"#
pattern N7 <- (eqName litN7 -> True)
  where N7 = fromName litN7

{-# noinline litN8 #-}
litN8 = fromStr " "#
pattern N8 <- (eqName litN8 -> True)
  where N8 = fromName litN8

{-# noinline litN9 #-}
litN9 = fromStr "do"#
pattern N9 <- (eqName litN9 -> True)
  where N9 = fromName litN9

{-# noinline litN10 #-}
litN10 = fromStr "where"#
pattern N10 <- (eqName litN10 -> True)
  where N10 = fromName litN10

{-# noinline litN11 #-}
litN11 = fromStr "of"#
pattern N11 <- (eqName litN11 -> True)
  where N11 = fromName litN11

{-# noinline litN12 #-}
litN12 = fromStr "("#
pattern N12 <- (eqName litN12 -> True)
  where N12 = fromName litN12

{-# noinline litN13 #-}
litN13 = fromStr ")"#
pattern N13 <- (eqName litN13 -> True)
  where N13 = fromName litN13

{-# noinline litN14 #-}
litN14 = fromStr "whereBeg"#
pattern N14 <- (eqName litN14 -> True)
  where N14 = fromName litN14

{-# noinline litN15 #-}
litN15 = fromStr "whereBegin"#
pattern N15 <- (eqName litN15 -> True)
  where N15 = fromName litN15

{-# noinline litN16 #-}
litN16 = fromStr "whereEnd"#
pattern N16 <- (eqName litN16 -> True)
  where N16 = fromName litN16

{-# noinline litN17 #-}
litN17 = fromStr "ofBeg"#
pattern N17 <- (eqName litN17 -> True)
  where N17 = fromName litN17

{-# noinline litN18 #-}
litN18 = fromStr "ofBegin"#
pattern N18 <- (eqName litN18 -> True)
  where N18 = fromName litN18

{-# noinline litN19 #-}
litN19 = fromStr "ofEnd"#
pattern N19 <- (eqName litN19 -> True)
  where N19 = fromName litN19

{-# noinline litN20 #-}
litN20 = fromStr "ModuleEnd"#
pattern N20 <- (eqName litN20 -> True)
  where N20 = fromName litN20

{-# noinline litN21 #-}
litN21 = fromStr ";"#
pattern N21 <- (eqName litN21 -> True)
  where N21 = fromName litN21

{-# noinline litN22 #-}
litN22 = fromStr "__"#
pattern N22 <- (eqName litN22 -> True)
  where N22 = fromName litN22

{-# noinline litN23 #-}
litN23 = fromStr "( )"#
pattern N23 <- (eqName litN23 -> True)
  where N23 = fromName litN23

{-# noinline litN24 #-}
litN24 = fromStr "___"#
pattern N24 <- (eqName litN24 -> True)
  where N24 = fromName litN24

{-# noinline litN25 #-}
litN25 = fromStr "<!"#
pattern N25 <- (eqName litN25 -> True)
  where N25 = fromName litN25

{-# noinline litN26 #-}
litN26 = fromStr "!>"#
pattern N26 <- (eqName litN26 -> True)
  where N26 = fromName litN26

{-# noinline litN27 #-}
litN27 = fromStr "{ }"#
pattern N27 <- (eqName litN27 -> True)
  where N27 = fromName litN27

{-# noinline litN28 #-}
litN28 = fromStr ":"#
pattern N28 <- (eqName litN28 -> True)
  where N28 = fromName litN28

{-# noinline litN29 #-}
litN29 = fromStr "{ : }"#
pattern N29 <- (eqName litN29 -> True)
  where N29 = fromName litN29

{-# noinline litN30 #-}
litN30 = fromStr "( : )"#
pattern N30 <- (eqName litN30 -> True)
  where N30 = fromName litN30

{-# noinline litN31 #-}
litN31 = fromStr "#"#
pattern N31 <- (eqName litN31 -> True)
  where N31 = fromName litN31

{-# noinline litN32 #-}
litN32 = fromStr "="#
pattern N32 <- (eqName litN32 -> True)
  where N32 = fromName litN32

{-# noinline litN33 #-}
litN33 = fromStr ":="#
pattern N33 <- (eqName litN33 -> True)
  where N33 = fromName litN33

{-# noinline litN34 #-}
litN34 = fromStr "import"#
pattern N34 <- (eqName litN34 -> True)
  where N34 = fromName litN34

{-# noinline litN35 #-}
litN35 = fromStr "whereBegin whereEnd"#
pattern N35 <- (eqName litN35 -> True)
  where N35 = fromName litN35

{-# noinline litN36 #-}
litN36 = fromStr "--->"#
pattern N36 <- (eqName litN36 -> True)
  where N36 = fromName litN36

{-# noinline litN37 #-}
litN37 = fromStr "\\ ->"#
pattern N37 <- (eqName litN37 -> True)
  where N37 = fromName litN37

{-# noinline litN38 #-}
litN38 = fromStr "->"#
pattern N38 <- (eqName litN38 -> True)
  where N38 = fromName litN38

{-# noinline litN39 #-}
litN39 = fromStr "_"#
pattern N39 <- (eqName litN39 -> True)
  where N39 = fromName litN39

{-# noinline litN40 #-}
litN40 = fromStr "==>"#
pattern N40 <- (eqName litN40 -> True)
  where N40 = fromName litN40

{-# noinline litN41 #-}
litN41 = fromStr "<-"#
pattern N41 <- (eqName litN41 -> True)
  where N41 = fromName litN41

{-# noinline litN42 #-}
litN42 = fromStr ">>="#
pattern N42 <- (eqName litN42 -> True)
  where N42 = fromName litN42

{-# noinline litN43 #-}
litN43 = fromStr "constructor"#
pattern N43 <- (eqName litN43 -> True)
  where N43 = fromName litN43

{-# noinline litN44 #-}
litN44 = fromStr "=>"#
pattern N44 <- (eqName litN44 -> True)
  where N44 = fromName litN44

{-# noinline litN45 #-}
litN45 = fromStr "~>"#
pattern N45 <- (eqName litN45 -> True)
  where N45 = fromName litN45

{-# noinline litN46 #-}
litN46 = fromStr "Rule"#
pattern N46 <- (eqName litN46 -> True)
  where N46 = fromName litN46

{-# noinline litN47 #-}
litN47 = fromStr "[ ]"#
pattern N47 <- (eqName litN47 -> True)
  where N47 = fromName litN47

{-# noinline litN48 #-}
litN48 = fromStr "-->"#
pattern N48 <- (eqName litN48 -> True)
  where N48 = fromName litN48

{-# noinline litN49 #-}
litN49 = fromStr "|"#
pattern N49 <- (eqName litN49 -> True)
  where N49 = fromName litN49

{-# noinline litN50 #-}
litN50 = fromStr "class whereBeg"#
pattern N50 <- (eqName litN50 -> True)
  where N50 = fromName litN50

{-# noinline litN51 #-}
litN51 = fromStr "instance whereBeg"#
pattern N51 <- (eqName litN51 -> True)
  where N51 = fromName litN51

{-# noinline litN52 #-}
litN52 = fromStr "data whereBeg"#
pattern N52 <- (eqName litN52 -> True)
  where N52 = fromName litN52

{-# noinline litN53 #-}
litN53 = fromStr "ofBegin ofEnd"#
pattern N53 <- (eqName litN53 -> True)
  where N53 = fromName litN53

{-# noinline litN54 #-}
litN54 = fromStr "case ofBeg"#
pattern N54 <- (eqName litN54 -> True)
  where N54 = fromName litN54

{-# noinline litN55 #-}
litN55 = fromStr "builtin"#
pattern N55 <- (eqName litN55 -> True)
  where N55 = fromName litN55

{-# noinline litN56 #-}
litN56 = fromStr "caseFun"#
pattern N56 <- (eqName litN56 -> True)
  where N56 = fromName litN56

{-# noinline litN57 #-}
litN57 = fromStr "App"#
pattern N57 <- (eqName litN57 -> True)
  where N57 = fromName litN57

{-# noinline litN58 #-}
litN58 = fromStr "Pi"#
pattern N58 <- (eqName litN58 -> True)
  where N58 = fromName litN58

{-# noinline litN59 #-}
litN59 = fromStr "HPi"#
pattern N59 <- (eqName litN59 -> True)
  where N59 = fromName litN59

{-# noinline litN60 #-}
litN60 = fromStr "CPi"#
pattern N60 <- (eqName litN60 -> True)
  where N60 = fromName litN60

{-# noinline litN61 #-}
litN61 = fromStr "IPi"#
pattern N61 <- (eqName litN61 -> True)
  where N61 = fromName litN61

{-# noinline litN62 #-}
litN62 = fromStr "IGNORE"#
pattern N62 <- (eqName litN62 -> True)
  where N62 = fromName litN62

{-# noinline litN63 #-}
litN63 = fromStr "()"#
pattern N63 <- (eqName litN63 -> True)
  where N63 = fromName litN63

{-# noinline litN64 #-}
litN64 = fromStr "( , )"#
pattern N64 <- (eqName litN64 -> True)
  where N64 = fromName litN64

{-# noinline litN65 #-}
litN65 = fromStr "[]"#
pattern N65 <- (eqName litN65 -> True)
  where N65 = fromName litN65

{-# noinline litN66 #-}
litN66 = fromStr ","#
pattern N66 <- (eqName litN66 -> True)
  where N66 = fromName litN66

{-# noinline litN67 #-}
litN67 = fromStr "newline"#
pattern N67 <- (eqName litN67 -> True)
  where N67 = fromName litN67

{-# noinline litN68 #-}
litN68 = fromStr "begin"#
pattern N68 <- (eqName litN68 -> True)
  where N68 = fromName litN68

{-# noinline litN69 #-}
litN69 = fromStr "end"#
pattern N69 <- (eqName litN69 -> True)
  where N69 = fromName litN69

{-# noinline litN70 #-}
litN70 = fromStr "quote"#
pattern N70 <- (eqName litN70 -> True)
  where N70 = fromName litN70

{-# noinline litN71 #-}
litN71 = fromStr "<>"#
pattern N71 <- (eqName litN71 -> True)
  where N71 = fromName litN71

{-# noinline litN72 #-}
litN72 = fromStr "Var"#
pattern N72 <- (eqName litN72 -> True)
  where N72 = fromName litN72

{-# noinline litN73 #-}
litN73 = fromStr "= ;"#
pattern N73 <- (eqName litN73 -> True)
  where N73 = fromName litN73

{-# noinline litN74 #-}
litN74 = fromStr "n"#
pattern N74 <- (eqName litN74 -> True)
  where N74 = fromName litN74

{-# noinline litN75 #-}
litN75 = fromStr "v"#
pattern N75 <- (eqName litN75 -> True)
  where N75 = fromName litN75

{-# noinline litN76 #-}
litN76 = fromStr "|->"#
pattern N76 <- (eqName litN76 -> True)
  where N76 = fromName litN76

{-# noinline litN77 #-}
litN77 = fromStr "@"#
pattern N77 <- (eqName litN77 -> True)
  where N77 = fromName litN77

{-# noinline litN78 #-}
litN78 = fromStr "c"#
pattern N78 <- (eqName litN78 -> True)
  where N78 = fromName litN78

{-# noinline litN79 #-}
litN79 = fromStr "Sup"#
pattern N79 <- (eqName litN79 -> True)
  where N79 = fromName litN79

{-# noinline litN80 #-}
litN80 = fromStr "Con"#
pattern N80 <- (eqName litN80 -> True)
  where N80 = fromName litN80

{-# noinline litN81 #-}
litN81 = fromStr "Meta"#
pattern N81 <- (eqName litN81 -> True)
  where N81 = fromName litN81

{-# noinline litN82 #-}
litN82 = fromStr "PrimOp"#
pattern N82 <- (eqName litN82 -> True)
  where N82 = fromName litN82

{-# noinline litN83 #-}
litN83 = fromStr "Fun"#
pattern N83 <- (eqName litN83 -> True)
  where N83 = fromName litN83

{-# noinline litN84 #-}
litN84 = fromStr "TGen"#
pattern N84 <- (eqName litN84 -> True)
  where N84 = fromName litN84

{-# noinline litN85 #-}
litN85 = fromStr "i"#
pattern N85 <- (eqName litN85 -> True)
  where N85 = fromName litN85

{-# noinline litN86 #-}
litN86 = fromStr "s"#
pattern N86 <- (eqName litN86 -> True)
  where N86 = fromName litN86

{-# noinline litN87 #-}
litN87 = fromStr "a"#
pattern N87 <- (eqName litN87 -> True)
  where N87 = fromName litN87

{-# noinline litN88 #-}
litN88 = fromStr "l"#
pattern N88 <- (eqName litN88 -> True)
  where N88 = fromName litN88

{-# noinline litN89 #-}
litN89 = fromStr "m"#
pattern N89 <- (eqName litN89 -> True)
  where N89 = fromName litN89

{-# noinline litN90 #-}
litN90 = fromStr "lookupDict"#
pattern N90 <- (eqName litN90 -> True)
  where N90 = fromName litN90

{-# noinline litN91 #-}
litN91 = fromStr "Fail"#
pattern N91 <- (eqName litN91 -> True)
  where N91 = fromName litN91

{-# noinline litN92 #-}
litN92 = fromStr "superClasses"#
pattern N92 <- (eqName litN92 -> True)
  where N92 = fromName litN92

{-# noinline litN93 #-}
litN93 = fromStr "SuccView"#
pattern N93 <- (eqName litN93 -> True)
  where N93 = fromName litN93

{-# noinline litN94 #-}
litN94 = fromStr "ConsView"#
pattern N94 <- (eqName litN94 -> True)
  where N94 = fromName litN94

{-# noinline litN95 #-}
litN95 = fromStr "wordToNat"#
pattern N95 <- (eqName litN95 -> True)
  where N95 = fromName litN95

{-# noinline litN96 #-}
litN96 = fromStr "matchRet"#
pattern N96 <- (eqName litN96 -> True)
  where N96 = fromName litN96

{-# noinline litN97 #-}
litN97 = fromStr "TRet"#
pattern N97 <- (eqName litN97 -> True)
  where N97 = fromName litN97

{-# noinline litN98 #-}
litN98 = fromStr "AppendStr"#
pattern N98 <- (eqName litN98 -> True)
  where N98 = fromName litN98

{-# noinline litN99 #-}
litN99 = fromStr "EqStr"#
pattern N99 <- (eqName litN99 -> True)
  where N99 = fromName litN99

{-# noinline litN100 #-}
litN100 = fromStr "TakeStr"#
pattern N100 <- (eqName litN100 -> True)
  where N100 = fromName litN100

{-# noinline litN101 #-}
litN101 = fromStr "DropStr"#
pattern N101 <- (eqName litN101 -> True)
  where N101 = fromName litN101

{-# noinline litN102 #-}
litN102 = fromStr "DecWord"#
pattern N102 <- (eqName litN102 -> True)
  where N102 = fromName litN102

{-# noinline litN103 #-}
litN103 = fromStr "AddWord"#
pattern N103 <- (eqName litN103 -> True)
  where N103 = fromName litN103

{-# noinline litN104 #-}
litN104 = fromStr "MulWord"#
pattern N104 <- (eqName litN104 -> True)
  where N104 = fromName litN104

{-# noinline litN105 #-}
litN105 = fromStr "DivWord"#
pattern N105 <- (eqName litN105 -> True)
  where N105 = fromName litN105

{-# noinline litN106 #-}
litN106 = fromStr "ModWord"#
pattern N106 <- (eqName litN106 -> True)
  where N106 = fromName litN106

{-# noinline litN107 #-}
litN107 = fromStr "EqWord"#
pattern N107 <- (eqName litN107 -> True)
  where N107 = fromName litN107

{-# noinline litN108 #-}
litN108 = fromStr "True"#
pattern N108 <- (eqName litN108 -> True)
  where N108 = fromName litN108

{-# noinline litN109 #-}
litN109 = fromStr "False"#
pattern N109 <- (eqName litN109 -> True)
  where N109 = fromName litN109

{-# noinline litN110 #-}
litN110 = fromStr "X"#
pattern N110 <- (eqName litN110 -> True)
  where N110 = fromName litN110

{-# noinline litN111 #-}
litN111 = fromStr "TMatch"#
pattern N111 <- (eqName litN111 -> True)
  where N111 = fromName litN111

{-# noinline litN112 #-}
litN112 = fromStr "Lam"#
pattern N112 <- (eqName litN112 -> True)
  where N112 = fromName litN112

{-# noinline litN113 #-}
litN113 = fromStr "Let"#
pattern N113 <- (eqName litN113 -> True)
  where N113 = fromName litN113

{-# noinline litN114 #-}
litN114 = fromStr "Erased"#
pattern N114 <- (eqName litN114 -> True)
  where N114 = fromName litN114

{-# noinline litN115 #-}
litN115 = fromStr "View"#
pattern N115 <- (eqName litN115 -> True)
  where N115 = fromName litN115

{-# noinline litN116 #-}
litN116 = fromStr "Guard"#
pattern N116 <- (eqName litN116 -> True)
  where N116 = fromName litN116

{-# noinline litN117 #-}
litN117 = fromStr "Dot"#
pattern N117 <- (eqName litN117 -> True)
  where N117 = fromName litN117

{-# noinline litN118 #-}
litN118 = fromStr "fail"#
pattern N118 <- (eqName litN118 -> True)
  where N118 = fromName litN118

{-# noinline litN119 #-}
litN119 = fromStr "Match"#
pattern N119 <- (eqName litN119 -> True)
  where N119 = fromName litN119

{-# noinline litN120 #-}
litN120 = fromStr "d"#
pattern N120 <- (eqName litN120 -> True)
  where N120 = fromName litN120

{-# noinline litN121 #-}
litN121 = fromStr "WSuc"#
pattern N121 <- (eqName litN121 -> True)
  where N121 = fromName litN121

{-# noinline litN122 #-}
litN122 = fromStr "WSucOk"#
pattern N122 <- (eqName litN122 -> True)
  where N122 = fromName litN122

{-# noinline litN123 #-}
litN123 = fromStr "ConsStr"#
pattern N123 <- (eqName litN123 -> True)
  where N123 = fromName litN123

{-# noinline litN124 #-}
litN124 = fromStr "ConsOk"#
pattern N124 <- (eqName litN124 -> True)
  where N124 = fromName litN124

{-# noinline litN125 #-}
litN125 = fromStr "MkOString"#
pattern N125 <- (eqName litN125 -> True)
  where N125 = fromName litN125

{-# noinline litN126 #-}
litN126 = fromStr "OEqStr"#
pattern N126 <- (eqName litN126 -> True)
  where N126 = fromName litN126

{-# noinline litN127 #-}
litN127 = fromStr "OTrue"#
pattern N127 <- (eqName litN127 -> True)
  where N127 = fromName litN127

{-# noinline litN128 #-}
litN128 = fromStr "MkOWord"#
pattern N128 <- (eqName litN128 -> True)
  where N128 = fromName litN128

{-# noinline litN129 #-}
litN129 = fromStr "OEqWord"#
pattern N129 <- (eqName litN129 -> True)
  where N129 = fromName litN129

{-# noinline litN130 #-}
litN130 = fromStr "SuperClassCons"#
pattern N130 <- (eqName litN130 -> True)
  where N130 = fromName litN130

{-# noinline litN131 #-}
litN131 = fromStr "SuperClassNil"#
pattern N131 <- (eqName litN131 -> True)
  where N131 = fromName litN131

{-# noinline litN132 #-}
litN132 = fromStr "p"#
pattern N132 <- (eqName litN132 -> True)
  where N132 = fromName litN132

{-# noinline litN133 #-}
litN133 = fromStr "Arr"#
pattern N133 <- (eqName litN133 -> True)
  where N133 = fromName litN133

{-# noinline litN134 #-}
litN134 = fromStr "Code"#
pattern N134 <- (eqName litN134 -> True)
  where N134 = fromName litN134

{-# noinline litN135 #-}
litN135 = fromStr "Ty"#
pattern N135 <- (eqName litN135 -> True)
  where N135 = fromName litN135

{-# noinline litN136 #-}
litN136 = fromStr "Type"#
pattern N136 <- (eqName litN136 -> True)
  where N136 = fromName litN136

{-# noinline litN137 #-}
litN137 = fromStr "String"#
pattern N137 <- (eqName litN137 -> True)
  where N137 = fromName litN137

{-# noinline litN138 #-}
litN138 = fromStr "OString"#
pattern N138 <- (eqName litN138 -> True)
  where N138 = fromName litN138

{-# noinline litN139 #-}
litN139 = fromStr "Word"#
pattern N139 <- (eqName litN139 -> True)
  where N139 = fromName litN139

{-# noinline litN140 #-}
litN140 = fromStr "Nat"#
pattern N140 <- (eqName litN140 -> True)
  where N140 = fromName litN140

{-# noinline litN141 #-}
litN141 = fromStr "OWord"#
pattern N141 <- (eqName litN141 -> True)
  where N141 = fromName litN141

{-# noinline litN142 #-}
litN142 = fromStr "z"#
pattern N142 <- (eqName litN142 -> True)
  where N142 = fromName litN142

{-# noinline litN143 #-}
litN143 = fromStr "Ap"#
pattern N143 <- (eqName litN143 -> True)
  where N143 = fromName litN143

{-# noinline litN144 #-}
litN144 = fromStr "e"#
pattern N144 <- (eqName litN144 -> True)
  where N144 = fromName litN144

{-# noinline litN145 #-}
litN145 = fromStr "h"#
pattern N145 <- (eqName litN145 -> True)
  where N145 = fromName litN145

{-# noinline litN146 #-}
litN146 = fromStr "TopLet"#
pattern N146 <- (eqName litN146 -> True)
  where N146 = fromName litN146

{-# noinline litN147 #-}
litN147 = fromStr "Bool"#
pattern N147 <- (eqName litN147 -> True)
  where N147 = fromName litN147

{-# noinline litN148 #-}
litN148 = fromStr "t"#
pattern N148 <- (eqName litN148 -> True)
  where N148 = fromName litN148

{-# noinline litN149 #-}
litN149 = fromStr "PCode"#
pattern N149 <- (eqName litN149 -> True)
  where N149 = fromName litN149

{-# noinline litN150 #-}
litN150 = fromStr "Computation"#
pattern N150 <- (eqName litN150 -> True)
  where N150 = fromName litN150

{-# noinline litN151 #-}
litN151 = fromStr "PLet"#
pattern N151 <- (eqName litN151 -> True)
  where N151 = fromName litN151

{-# noinline litN152 #-}
litN152 = fromStr "PLam"#
pattern N152 <- (eqName litN152 -> True)
  where N152 = fromName litN152

{-# noinline litN153 #-}
litN153 = fromStr "PApp"#
pattern N153 <- (eqName litN153 -> True)
  where N153 = fromName litN153

{-# noinline litN154 #-}
litN154 = fromStr "Prod"#
pattern N154 <- (eqName litN154 -> True)
  where N154 = fromName litN154

{-# noinline litN155 #-}
litN155 = fromStr "Pair"#
pattern N155 <- (eqName litN155 -> True)
  where N155 = fromName litN155

{-# noinline litN156 #-}
litN156 = fromStr "Fst"#
pattern N156 <- (eqName litN156 -> True)
  where N156 = fromName litN156

{-# noinline litN157 #-}
litN157 = fromStr "Snd"#
pattern N157 <- (eqName litN157 -> True)
  where N157 = fromName litN157

{-# noinline litN158 #-}
litN158 = fromStr "noreturn"#
pattern N158 <- (eqName litN158 -> True)
  where N158 = fromName litN158

{-# LINE 6 "src/C2_NameLiterals.hs" #-}

