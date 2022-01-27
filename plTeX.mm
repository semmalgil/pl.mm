$c wff $.
$c ( $.
$c ) $.
$c ~ $.
$c /\ $.
$c \/ $.
$c -> $.
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
$v mu $.
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
wmu $f wff mu $.
wla $f wff lam $.
wka $f wff kap $.

$( If ` phi ` is a wff (well-formed formula), so is ` ~ phi ` or
   "not ` phi ` ." $)
wnTeX $a wff ~ phi $.
$( If ` phi ` and ` psi ` are wff's, so is ` ( phi /\ psi ) ` or
   " ` phi ` and ` psi ` ." $)
waTeX $a wff ( phi /\ psi ) $.
$( If ` phi ` and ` psi ` are wff's, so is ` ( phi \/ psi ) ` or
   " ` phi ` or ` psi ` ." $)
woTeX $a wff ( phi \/ psi ) $.
$( If ` phi ` and ` psi ` are wff's, so is ` ( phi -> psi ) ` or
   " ` phi ` implies ` psi ` ." $)
wiTeX $a wff ( phi -> psi ) $.
$( If ` phi ` and ` psi ` are wff's, so is ` ( phi <-> psi ) ` or
   " ` phi ` if and only if ` psi ` ." $)
wbTeX $a wff ( phi <-> psi ) $.

$c rc $.
$c c $.
$c bl $.

$v C $.
$v C1 $.
$v C2 $.

rcC $f rc C $.
rcC1 $f rc C1 $.
rcC2 $f rc C2 $.

rcc $a rc c $.
rch $a rc C1 bl C2 $.

$c rw $.
$c rwTeX $.
$c bt $.
$c et $.
$c { $.
$c } $.
$c | $.
$c hl $.
$c ' $.
$c & $.
$c \\ $.

$v Phi $.
$v Psi $.

rwPh $f rw Phi $.
rwPs $f rw Psi $.

$( If ` phi ` is a wff, it is also a row of wff's. $)
rwwTeX $a rw phi $.
rwh $a rw Phi ' & ' Psi $.
$( If ` Phi ` and ` Psi ` are rows of wff's, so is
   their horizontal concatenation. $)
rwhTeX $a rwTeX bt { c bl c }
  ' Phi ' & ' Psi ' et $.

$c tv $.
$c T $.
$c F $.

$v b $.
$v b1 $.
$v b2 $.

tvb $f tv b $.
tvb1 $f tv b1 $.
tvb2 $f tv b2 $.

$( ` T ` (true) is a truth value. $)
tvTTeX $a tv T $.
$( ` F ` (false) is a truth value. $)
tvFTeX $a tv F $.

$c rtv $.
$c rtvTeX $.

$v B $.
$v B1 $.
$v B2 $.

rtB $f rtv B $.
rtB1 $f rtv B1 $.
rtB2 $f rtv B2 $.

$( If ` b ` is a truth value, it is also a row of truth values. $)
rttTeX $a rtv b $.
rth $a rtv B1 ' & ' B2 $.
$( If ` B1 ` and ` B2 ` are rows of truth values, so is
   their horizontal concatenation. $)
rthTeX $a rtvTeX bt { c bl c }
  ' B1 ' & ' B2 ' et $.

$c atv $.
$c atvTeX $.

$v bB1 $.
$v bB2 $.

aB1 $f atv bB1 $.
aB2 $f atv bB2 $.

$( If ` B ` is a row of truth values, it is also an array of truth values. $)
arTeX $a atv B $.
av $a atv
  bB1 ' \\ '
  bB2 $.
$( If ` bB1 ` and ` bB2 ` are arrays of truth values, so is
   their vertical concatenation. $)
avTeX $a atvTeX bt { c }
  ' bB1 ' \\
  ' bB2 ' et $.

$c tt $.

$( Truth table stating that the truth value of a wff ` phi ` is ` b ` . $)
ttwTeX $a tt bt { | c | } hl
  ' phi ' \\ hl
  '  b  ' \\ hl et $.

${
  tthTeX.1 $e tt bt { | C1 | } hl
    ' Phi ' \\ hl
    ' B1  ' \\ hl et $.
  tthTeX.2 $e tt bt { | C2 | } hl
    ' Psi ' \\ hl
    ' B2  ' \\ hl et $.
  $( Horizontal concatenation of two truth tables containing only one row of
     truth values. The resulting truth table states that the wff's in the row
     ` bt { c bl c } ' Phi ' & ' Psi ' et ` have the respective truth values
     in the row ` bt { c bl c } ' B1 ' & ' B2 ' et `, where ` Phi ` and ` Psi `
     are rows of wff's, and ` B1 ` and ` B2 ` are rows of truth values. $)
  tthTeX $a tt bt { | C1 bl C2 | } hl
    ' Phi ' & ' Psi ' \\ hl
    ' B1  ' & ' B2  ' \\ hl et $.
$}

${
  ttvTeX.1 $e tt bt { | C | } hl
    ' Phi ' \\ hl
    ' bB1 ' \\ hl et $.
  ttvTeX.2 $e tt bt { | C | } hl
    ' Phi ' \\ hl
    ' bB2 ' \\ hl et $.
  $( Vertical concatenation of two truth tables. The resulting truth table
     states that the wff's in the row ` Phi ` have the respective truth values
     in either one of the rows in the array ` bt { c } ' bB1 ' \\ ' bB2 ' et `,
     where ` Phi ` is a row of wff's, and ` bB1 ` and ` bB2 ` are arrays of
     truth values. $)
  ttvTeX $a tt bt { | C | } hl
    ' Phi ' \\ hl
    ' bB1 ' \\
    ' bB2 ' \\ hl et $.
$}

${
  $( Example of truth tables for two wff's. This truth table states that either
     both of the wff's ` phi ` and ` psi ` are true, only one of them is true,
     or both are false. $)
  tt2wTeX $p tt bt { | c bl c | } hl
    ' phi ' & ' psi ' \\ hl
    '  T  ' & '  T  ' \\
    '  T  ' & '  F  ' \\
    '  F  ' & '  T  ' \\
    '  F  ' & '  F  ' \\ hl et $=
  rcc rcc rch wph rwwTeX wps rwwTeX rwh tvTTeX rttTeX tvTTeX rttTeX rth arTeX
  tvTTeX rttTeX tvFTeX rttTeX rth arTeX tvFTeX rttTeX tvTTeX rttTeX rth arTeX
  tvFTeX rttTeX tvFTeX rttTeX rth arTeX av av rcc rcc wph rwwTeX wps rwwTeX
  tvTTeX rttTeX tvTTeX rttTeX wph tvTTeX ttwTeX wps tvTTeX ttwTeX tthTeX rcc
  rcc rch wph rwwTeX wps rwwTeX rwh tvTTeX rttTeX tvFTeX rttTeX rth arTeX
  tvFTeX rttTeX tvTTeX rttTeX rth arTeX tvFTeX rttTeX tvFTeX rttTeX rth arTeX
  av rcc rcc wph rwwTeX wps rwwTeX tvTTeX rttTeX tvFTeX rttTeX wph tvTTeX
  ttwTeX wps tvFTeX ttwTeX tthTeX rcc rcc rch wph rwwTeX wps rwwTeX rwh
  tvFTeX rttTeX tvTTeX rttTeX rth arTeX tvFTeX rttTeX tvFTeX rttTeX rth arTeX
  rcc rcc wph rwwTeX wps rwwTeX tvFTeX rttTeX tvTTeX rttTeX wph tvFTeX ttwTeX
  wps tvTTeX ttwTeX tthTeX rcc rcc wph rwwTeX wps rwwTeX tvFTeX rttTeX tvFTeX
  rttTeX wph tvFTeX ttwTeX wps tvFTeX ttwTeX tthTeX ttvTeX ttvTeX ttvTeX $.
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

  latexdef "rc" as "";
  latexdef "c" as "c";
  latexdef "bl" as "";
  latexdef "C" as "c";
  latexdef "C1" as "c";
  latexdef "C2" as "c";

  latexdef "rw" as "{\rm rw}\ ";
  latexdef "rwTeX" as "{\rm rw}\ ";
  latexdef "bt" as "\begin{tabular}";
  latexdef "et" as "\end{tabular}";
  latexdef "{" as "{";
  latexdef "}" as "}";
  latexdef "|" as "|";
  latexdef "hl" as "\hline";
  latexdef "'" as "$";
  latexdef "&" as "&";
  latexdef "\\" as "\\";

  latexdef "Phi" as "\Phi";
  latexdef "Psi" as "\Psi";

  latexdef "tv" as "{\rm tv}\ ";

  latexdef "T" as "\mathrm{T}";
  latexdef "F" as "\mathrm{F}";

  latexdef "b" as "\mathrm{b}";
  latexdef "b1" as "\mathrm{b_1}";
  latexdef "b2" as "\mathrm{b_2}";

  latexdef "rtv" as "{\rm rtv}\ ";
  latexdef "rtvTeX" as "{\rm rtv}\ ";

  latexdef "B" as "\mathrm{B}";
  latexdef "B1" as "\mathrm{B_1}";
  latexdef "B2" as "\mathrm{B_2}";

  latexdef "atv" as "{\rm atv}\ ";
  latexdef "atvTeX" as "{\rm atv}\ ";

  latexdef "bB1" as "\mathbf{B_1}";
  latexdef "bB2" as "\mathbf{B_2}";

  latexdef "tt" as "{\rm tt}\ ";

$)
