$c wff $.
$c (   $.
$c )   $.
$c ~   $.
$c /\  $.
$c \/  $.
$c ->  $.
$c <-> $.

$v phi $.
$v psi $.
$v chi $.
$v the $.
$v tau $.
$v eta $.
$v zet $.
$v sig $.
$v rho $.
$v mu  $.
$v lam $.
$v kap $.

wph $f wff phi $.
wps $f wff psi $.
wch $f wff chi $.
wth $f wff the $.
wta $f wff tau $.
wet $f wff eta $.
wze $f wff zet $.
wsi $f wff sig $.
wrh $f wff rho $.
wmu $f wff mu  $.
wla $f wff lam $.
wka $f wff kap $.

$( If ` phi ` is a wff (well-formed formula), so is ` ~ phi ` or
   "not ` phi `." $)
wn $a wff ~ phi           $.
$( If ` phi ` and ` psi ` are wff's, so is ` ( phi /\ psi ) ` or
   "` phi ` and ` psi `." $)
wa $a wff ( phi /\ psi )  $.
$( If ` phi ` and ` psi ` are wff's, so is ` ( phi \/ psi ) ` or
   "` phi ` or ` psi `." $)
wo $a wff ( phi \/ psi )  $.
$( If ` phi ` and ` psi ` are wff's, so is ` ( phi -> psi ) ` or
   "` phi ` implies ` psi `." $)
wi $a wff ( phi -> psi )  $.
$( If ` phi ` and ` psi ` are wff's, so is ` ( phi <-> psi ) ` or
   "` phi ` if and only if ` psi `." $)
wb $a wff ( phi <-> psi ) $.

$c rw  $.

$v Phi $.
$v Psi $.

rwPh $f rw Phi $.
rwPs $f rw Psi $.

$( If ` phi ` is a wff, it is also a row of wff's. $)
rww $a rw phi     $.
$( If ` Phi ` and ` Psi ` are rows of wff's, so is
   their horizontal concatenation. $)
rwh $a rw Phi Psi $.

$c tv $.
$c T  $.
$c F  $.

$v b  $.
$v b1 $.
$v b2 $.

tvb  $f tv b  $.
tvb1 $f tv b1 $.
tvb2 $f tv b2 $.

$( ` T ` (true) is a truth value. $)
tvT $a tv T $.
$( ` F ` (false) is a truth value. $)
tvF $a tv F $.

$c rtv $.

$v B  $.
$v B1 $.
$v B2 $.

rtB  $f rtv B  $.
rtB1 $f rtv B1 $.
rtB2 $f rtv B2 $.

$( If ` b ` is a truth value, it is also a row of truth values. $)
rtt $a rtv b     $.
$( If ` B1 ` and ` B2 ` are rows of truth values, so is
   their horizontal concatenation. $)
rth $a rtv B1 B2 $.

$c atv $.
$c [   $.
$c ]   $.
$c |   $.

$v bB1 $.
$v bB2 $.

aB1 $f atv bB1 $.
aB2 $f atv bB2 $.

$( If ` B ` is a row of truth values, it is also an array of truth values. $)
ar $a atv B $.
$( If ` bB1 ` and ` bB2 ` are arrays of truth values, so is
   their vertical concatenation. $)
av $a atv
  bB1 |
  bB2 $.

$c tt $.

$( Truth table stating that the truth value of a wff ` phi ` is ` b `. $)
ttw $a tt
  [ phi |
     b  ] $.

${
  tth.1 $e tt
    [ Phi |
      B1  ] $.
  tth.2 $e tt
    [ Psi |
      B2  ] $.
  $( Horizontal concatenation of two truth tables containing only one row of
     truth values. The resulting truth table states that the wff's in the row
     ` Phi Psi ` have the respective truth values in the row ` B1 B2 `, where
     ` Phi ` and ` Psi ` are rows of wff's, and ` B1 ` and ` B2 ` are rows of
     truth values. $)
  tth   $a tt
    [ Phi Psi |
      B1  B2  ] $.
$}

${
  ttv.1 $e tt
    [ Phi |
      bB1 ] $.
  ttv.2 $e tt
    [ Phi |
      bB2 ] $.
  $( Vertical concatenation of two truth tables. The resulting truth table
     states that the wff's in the row ` Phi ` have the respective truth values
     in either one of the rows in the array ` bB1 | bB2 `, where ` Phi ` is
     a row of wff's, and ` bB1 ` and ` bB2 ` are arrays of truth values. $)
  ttv   $a tt
    [ Phi |
      bB1 |
      bB2 ] $.
$}

${
  $( Example of truth tables for two wff's. This truth table states that either
     both of the wff's ` phi ` and ` psi ` are true, only one of them is true,
     or both are false. $)
  tt2w $p tt
    [ phi psi |
       T   T  |
       T   F  |
       F   T  |
       F   F  ] $=
    wph rww wps rww rwh tvT rtt tvT rtt rth ar tvT rtt tvF rtt rth ar tvF rtt
    tvT rtt rth ar tvF rtt tvF rtt rth ar av av wph rww wps rww tvT rtt tvT rtt
    wph tvT ttw wps tvT ttw tth wph rww wps rww rwh tvT rtt tvF rtt rth ar tvF
    rtt tvT rtt rth ar tvF rtt tvF rtt rth ar av wph rww wps rww tvT rtt tvF
    rtt wph tvT ttw wps tvF ttw tth wph rww wps rww rwh tvF rtt tvT rtt rth ar
    tvF rtt tvF rtt rth ar wph rww wps rww tvF rtt tvT rtt wph tvF ttw wps tvT
    ttw tth wph rww wps rww tvF rtt tvF rtt wph tvF ttw wps tvF ttw tth ttv ttv
    ttv $.
$}

$( $t

  latexdef "wff" as "{\rm wff}\ ";
  latexdef "(" as "\left(";
  latexdef ")" as "\right)";
  latexdef "~" as "\lnot";
  latexdef "/\" as "\wedge";
  latexdef "\/" as "\vee";
  latexdef "->" as " \rightarrow ";
  latexdef "<->" as "\leftrightarrow";

  latexdef "phi" as "\varphi";
  latexdef "psi" as "\psi";
  latexdef "chi" as "\chi";
  latexdef "the" as "\theta";
  latexdef "tau" as "\tau";
  latexdef "eta" as "\eta";
  latexdef "zet" as "\zeta";
  latexdef "sig" as "\sigma";
  latexdef "rho" as "\rho";
  latexdef "mu" as "\mu";
  latexdef "lam" as "\lambda";
  latexdef "kap" as "\kappa";

  latexdef "rw" as "{\rm rw}\ ";

  latexdef "Phi" as "\Phi";
  latexdef "Psi" as "\Psi";

  latexdef "tv" as "{\rm tv}\ ";

  latexdef "T" as "\mathrm{T}";
  latexdef "F" as "\mathrm{F}";

  latexdef "b" as "\mathrm{b}";
  latexdef "b1" as "\mathrm{b_1}";
  latexdef "b2" as "\mathrm{b_2}";

  latexdef "rtv" as "{\rm rtv}\ ";

  latexdef "B" as "\mathrm{B}";
  latexdef "B1" as "\mathrm{B_1}";
  latexdef "B2" as "\mathrm{B_2}";

  latexdef "atv" as "{\rm atv}\ ";

  latexdef "[" as "\left[";
  latexdef "]" as "\right]";
  latexdef "|" as "\mid";

  latexdef "bB1" as "\mathbf{B_1}";
  latexdef "bB2" as "\mathbf{B_2}";

  latexdef "tt" as "{\rm tt}\ ";

$)
