%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CzdnlQrlBi

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:49 EST 2020

% Result     : Theorem 3.52s
% Output     : Refutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 119 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  572 ( 991 expanded)
%              Number of equality atoms :   34 (  49 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k4_xboole_0 @ X39 @ ( k4_xboole_0 @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X28 @ X29 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_xboole_0 @ X27 @ X26 )
        = X26 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X45: $i] :
      ( ( ( k9_relat_1 @ X45 @ ( k1_relat_1 @ X45 ) )
        = ( k2_relat_1 @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k9_relat_1 @ X52 @ ( k10_relat_1 @ X52 @ X51 ) )
        = ( k3_xboole_0 @ X51 @ ( k9_relat_1 @ X52 @ ( k1_relat_1 @ X52 ) ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('13',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C_1 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X46 @ X47 )
      | ~ ( v1_relat_1 @ X48 )
      | ( r1_tarski @ ( k9_relat_1 @ X48 @ X46 ) @ ( k9_relat_1 @ X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ( X18 != X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X19: $i] :
      ( r1_tarski @ X19 @ X19 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_xboole_0 @ X27 @ X26 )
        = X26 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('27',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X33 @ X34 ) @ X35 )
      | ~ ( r1_tarski @ X33 @ ( k2_xboole_0 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X32: $i] :
      ( ( k4_xboole_0 @ X32 @ k1_xboole_0 )
      = X32 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k4_xboole_0 @ X39 @ ( k4_xboole_0 @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k4_xboole_0 @ X39 @ ( k4_xboole_0 @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X32: $i] :
      ( ( k4_xboole_0 @ X32 @ k1_xboole_0 )
      = X32 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','38','39','40','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r1_tarski @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['7','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CzdnlQrlBi
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.52/3.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.52/3.75  % Solved by: fo/fo7.sh
% 3.52/3.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.52/3.75  % done 3554 iterations in 3.285s
% 3.52/3.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.52/3.75  % SZS output start Refutation
% 3.52/3.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.52/3.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.52/3.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.52/3.75  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.52/3.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.52/3.75  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.52/3.75  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.52/3.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.52/3.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.52/3.75  thf(sk_B_type, type, sk_B: $i).
% 3.52/3.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.52/3.75  thf(sk_A_type, type, sk_A: $i).
% 3.52/3.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.52/3.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.52/3.75  thf(t158_funct_1, conjecture,
% 3.52/3.75    (![A:$i,B:$i,C:$i]:
% 3.52/3.75     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.52/3.75       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 3.52/3.75           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 3.52/3.75         ( r1_tarski @ A @ B ) ) ))).
% 3.52/3.75  thf(zf_stmt_0, negated_conjecture,
% 3.52/3.75    (~( ![A:$i,B:$i,C:$i]:
% 3.52/3.75        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.52/3.75          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 3.52/3.75              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 3.52/3.75            ( r1_tarski @ A @ B ) ) ) )),
% 3.52/3.75    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 3.52/3.75  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 3.52/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.52/3.75  thf(t48_xboole_1, axiom,
% 3.52/3.75    (![A:$i,B:$i]:
% 3.52/3.75     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.52/3.75  thf('1', plain,
% 3.52/3.75      (![X39 : $i, X40 : $i]:
% 3.52/3.75         ((k4_xboole_0 @ X39 @ (k4_xboole_0 @ X39 @ X40))
% 3.52/3.75           = (k3_xboole_0 @ X39 @ X40))),
% 3.52/3.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.52/3.75  thf(t36_xboole_1, axiom,
% 3.52/3.75    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.52/3.75  thf('2', plain,
% 3.52/3.75      (![X28 : $i, X29 : $i]: (r1_tarski @ (k4_xboole_0 @ X28 @ X29) @ X28)),
% 3.52/3.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.52/3.75  thf(t12_xboole_1, axiom,
% 3.52/3.75    (![A:$i,B:$i]:
% 3.52/3.75     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.52/3.75  thf('3', plain,
% 3.52/3.75      (![X26 : $i, X27 : $i]:
% 3.52/3.75         (((k2_xboole_0 @ X27 @ X26) = (X26)) | ~ (r1_tarski @ X27 @ X26))),
% 3.52/3.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.52/3.75  thf('4', plain,
% 3.52/3.75      (![X0 : $i, X1 : $i]:
% 3.52/3.75         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 3.52/3.75      inference('sup-', [status(thm)], ['2', '3'])).
% 3.52/3.75  thf(commutativity_k2_xboole_0, axiom,
% 3.52/3.75    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.52/3.75  thf('5', plain,
% 3.52/3.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.52/3.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.52/3.75  thf('6', plain,
% 3.52/3.75      (![X0 : $i, X1 : $i]:
% 3.52/3.75         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 3.52/3.75      inference('demod', [status(thm)], ['4', '5'])).
% 3.52/3.75  thf('7', plain,
% 3.52/3.75      (![X0 : $i, X1 : $i]:
% 3.52/3.75         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 3.52/3.75      inference('sup+', [status(thm)], ['1', '6'])).
% 3.52/3.75  thf(t146_relat_1, axiom,
% 3.52/3.75    (![A:$i]:
% 3.52/3.75     ( ( v1_relat_1 @ A ) =>
% 3.52/3.75       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 3.52/3.75  thf('8', plain,
% 3.52/3.75      (![X45 : $i]:
% 3.52/3.75         (((k9_relat_1 @ X45 @ (k1_relat_1 @ X45)) = (k2_relat_1 @ X45))
% 3.52/3.75          | ~ (v1_relat_1 @ X45))),
% 3.52/3.75      inference('cnf', [status(esa)], [t146_relat_1])).
% 3.52/3.75  thf(t148_funct_1, axiom,
% 3.52/3.75    (![A:$i,B:$i]:
% 3.52/3.75     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.52/3.75       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 3.52/3.75         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 3.52/3.75  thf('9', plain,
% 3.52/3.75      (![X51 : $i, X52 : $i]:
% 3.52/3.75         (((k9_relat_1 @ X52 @ (k10_relat_1 @ X52 @ X51))
% 3.52/3.75            = (k3_xboole_0 @ X51 @ (k9_relat_1 @ X52 @ (k1_relat_1 @ X52))))
% 3.52/3.75          | ~ (v1_funct_1 @ X52)
% 3.52/3.75          | ~ (v1_relat_1 @ X52))),
% 3.52/3.75      inference('cnf', [status(esa)], [t148_funct_1])).
% 3.52/3.75  thf('10', plain,
% 3.52/3.75      (![X0 : $i, X1 : $i]:
% 3.52/3.75         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 3.52/3.75            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 3.52/3.75          | ~ (v1_relat_1 @ X0)
% 3.52/3.75          | ~ (v1_relat_1 @ X0)
% 3.52/3.75          | ~ (v1_funct_1 @ X0))),
% 3.52/3.75      inference('sup+', [status(thm)], ['8', '9'])).
% 3.52/3.75  thf('11', plain,
% 3.52/3.75      (![X0 : $i, X1 : $i]:
% 3.52/3.75         (~ (v1_funct_1 @ X0)
% 3.52/3.75          | ~ (v1_relat_1 @ X0)
% 3.52/3.75          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 3.52/3.75              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 3.52/3.75      inference('simplify', [status(thm)], ['10'])).
% 3.52/3.75  thf('12', plain,
% 3.52/3.75      (![X0 : $i, X1 : $i]:
% 3.52/3.75         (~ (v1_funct_1 @ X0)
% 3.52/3.75          | ~ (v1_relat_1 @ X0)
% 3.52/3.75          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 3.52/3.75              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 3.52/3.75      inference('simplify', [status(thm)], ['10'])).
% 3.52/3.75  thf('13', plain,
% 3.52/3.75      ((r1_tarski @ (k10_relat_1 @ sk_C_1 @ sk_A) @ 
% 3.52/3.75        (k10_relat_1 @ sk_C_1 @ sk_B))),
% 3.52/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.52/3.75  thf(t156_relat_1, axiom,
% 3.52/3.75    (![A:$i,B:$i,C:$i]:
% 3.52/3.75     ( ( v1_relat_1 @ C ) =>
% 3.52/3.75       ( ( r1_tarski @ A @ B ) =>
% 3.52/3.75         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 3.52/3.75  thf('14', plain,
% 3.52/3.75      (![X46 : $i, X47 : $i, X48 : $i]:
% 3.52/3.75         (~ (r1_tarski @ X46 @ X47)
% 3.52/3.75          | ~ (v1_relat_1 @ X48)
% 3.52/3.75          | (r1_tarski @ (k9_relat_1 @ X48 @ X46) @ (k9_relat_1 @ X48 @ X47)))),
% 3.52/3.75      inference('cnf', [status(esa)], [t156_relat_1])).
% 3.52/3.75  thf('15', plain,
% 3.52/3.75      (![X0 : $i]:
% 3.52/3.75         ((r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C_1 @ sk_A)) @ 
% 3.52/3.75           (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C_1 @ sk_B)))
% 3.52/3.75          | ~ (v1_relat_1 @ X0))),
% 3.52/3.75      inference('sup-', [status(thm)], ['13', '14'])).
% 3.52/3.75  thf('16', plain,
% 3.52/3.75      (((r1_tarski @ (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C_1)) @ 
% 3.52/3.75         (k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_B)))
% 3.52/3.75        | ~ (v1_relat_1 @ sk_C_1)
% 3.52/3.75        | ~ (v1_funct_1 @ sk_C_1)
% 3.52/3.75        | ~ (v1_relat_1 @ sk_C_1))),
% 3.52/3.75      inference('sup+', [status(thm)], ['12', '15'])).
% 3.52/3.75  thf(d10_xboole_0, axiom,
% 3.52/3.75    (![A:$i,B:$i]:
% 3.52/3.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.52/3.75  thf('17', plain,
% 3.52/3.75      (![X18 : $i, X19 : $i]: ((r1_tarski @ X18 @ X19) | ((X18) != (X19)))),
% 3.52/3.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.52/3.75  thf('18', plain, (![X19 : $i]: (r1_tarski @ X19 @ X19)),
% 3.52/3.75      inference('simplify', [status(thm)], ['17'])).
% 3.52/3.75  thf(t11_xboole_1, axiom,
% 3.52/3.75    (![A:$i,B:$i,C:$i]:
% 3.52/3.75     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 3.52/3.75  thf('19', plain,
% 3.52/3.75      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.52/3.75         ((r1_tarski @ X23 @ X24)
% 3.52/3.75          | ~ (r1_tarski @ (k2_xboole_0 @ X23 @ X25) @ X24))),
% 3.52/3.75      inference('cnf', [status(esa)], [t11_xboole_1])).
% 3.52/3.75  thf('20', plain,
% 3.52/3.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 3.52/3.75      inference('sup-', [status(thm)], ['18', '19'])).
% 3.52/3.75  thf('21', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C_1))),
% 3.52/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.52/3.75  thf('22', plain,
% 3.52/3.75      (![X26 : $i, X27 : $i]:
% 3.52/3.75         (((k2_xboole_0 @ X27 @ X26) = (X26)) | ~ (r1_tarski @ X27 @ X26))),
% 3.52/3.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.52/3.75  thf('23', plain,
% 3.52/3.75      (((k2_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1))),
% 3.52/3.75      inference('sup-', [status(thm)], ['21', '22'])).
% 3.52/3.75  thf('24', plain,
% 3.52/3.75      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.52/3.75         ((r1_tarski @ X23 @ X24)
% 3.52/3.75          | ~ (r1_tarski @ (k2_xboole_0 @ X23 @ X25) @ X24))),
% 3.52/3.75      inference('cnf', [status(esa)], [t11_xboole_1])).
% 3.52/3.75  thf('25', plain,
% 3.52/3.75      (![X0 : $i]:
% 3.52/3.75         (~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ X0) | (r1_tarski @ sk_A @ X0))),
% 3.52/3.75      inference('sup-', [status(thm)], ['23', '24'])).
% 3.52/3.75  thf('26', plain,
% 3.52/3.75      (![X0 : $i]:
% 3.52/3.75         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k2_relat_1 @ sk_C_1) @ X0))),
% 3.52/3.75      inference('sup-', [status(thm)], ['20', '25'])).
% 3.52/3.75  thf(t43_xboole_1, axiom,
% 3.52/3.75    (![A:$i,B:$i,C:$i]:
% 3.52/3.75     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 3.52/3.75       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 3.52/3.75  thf('27', plain,
% 3.52/3.75      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.52/3.75         ((r1_tarski @ (k4_xboole_0 @ X33 @ X34) @ X35)
% 3.52/3.75          | ~ (r1_tarski @ X33 @ (k2_xboole_0 @ X34 @ X35)))),
% 3.52/3.75      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.52/3.75  thf('28', plain,
% 3.52/3.75      (![X0 : $i]:
% 3.52/3.75         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C_1)) @ X0)),
% 3.52/3.75      inference('sup-', [status(thm)], ['26', '27'])).
% 3.52/3.75  thf(t3_boole, axiom,
% 3.52/3.75    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.52/3.75  thf('29', plain, (![X32 : $i]: ((k4_xboole_0 @ X32 @ k1_xboole_0) = (X32))),
% 3.52/3.75      inference('cnf', [status(esa)], [t3_boole])).
% 3.52/3.75  thf('30', plain,
% 3.52/3.75      (![X39 : $i, X40 : $i]:
% 3.52/3.75         ((k4_xboole_0 @ X39 @ (k4_xboole_0 @ X39 @ X40))
% 3.52/3.75           = (k3_xboole_0 @ X39 @ X40))),
% 3.52/3.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.52/3.75  thf('31', plain,
% 3.52/3.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.52/3.75      inference('sup+', [status(thm)], ['29', '30'])).
% 3.52/3.75  thf(t38_xboole_1, axiom,
% 3.52/3.75    (![A:$i,B:$i]:
% 3.52/3.75     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 3.52/3.75       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.52/3.75  thf('32', plain,
% 3.52/3.75      (![X30 : $i, X31 : $i]:
% 3.52/3.75         (((X30) = (k1_xboole_0))
% 3.52/3.75          | ~ (r1_tarski @ X30 @ (k4_xboole_0 @ X31 @ X30)))),
% 3.52/3.75      inference('cnf', [status(esa)], [t38_xboole_1])).
% 3.52/3.75  thf('33', plain,
% 3.52/3.75      (![X0 : $i]:
% 3.52/3.75         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 3.52/3.75          | ((X0) = (k1_xboole_0)))),
% 3.52/3.75      inference('sup-', [status(thm)], ['31', '32'])).
% 3.52/3.75  thf('34', plain,
% 3.52/3.75      (((k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C_1)) = (k1_xboole_0))),
% 3.52/3.75      inference('sup-', [status(thm)], ['28', '33'])).
% 3.52/3.75  thf('35', plain,
% 3.52/3.75      (![X39 : $i, X40 : $i]:
% 3.52/3.75         ((k4_xboole_0 @ X39 @ (k4_xboole_0 @ X39 @ X40))
% 3.52/3.75           = (k3_xboole_0 @ X39 @ X40))),
% 3.52/3.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.52/3.75  thf('36', plain,
% 3.52/3.75      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 3.52/3.75         = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C_1)))),
% 3.52/3.75      inference('sup+', [status(thm)], ['34', '35'])).
% 3.52/3.75  thf('37', plain, (![X32 : $i]: ((k4_xboole_0 @ X32 @ k1_xboole_0) = (X32))),
% 3.52/3.75      inference('cnf', [status(esa)], [t3_boole])).
% 3.52/3.75  thf('38', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C_1)))),
% 3.52/3.75      inference('demod', [status(thm)], ['36', '37'])).
% 3.52/3.75  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 3.52/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.52/3.75  thf('40', plain, ((v1_funct_1 @ sk_C_1)),
% 3.52/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.52/3.75  thf('41', plain, ((v1_relat_1 @ sk_C_1)),
% 3.52/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.52/3.75  thf('42', plain,
% 3.52/3.75      ((r1_tarski @ sk_A @ 
% 3.52/3.75        (k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_B)))),
% 3.52/3.75      inference('demod', [status(thm)], ['16', '38', '39', '40', '41'])).
% 3.52/3.75  thf('43', plain,
% 3.52/3.75      (((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C_1)))
% 3.52/3.75        | ~ (v1_relat_1 @ sk_C_1)
% 3.52/3.75        | ~ (v1_funct_1 @ sk_C_1))),
% 3.52/3.75      inference('sup+', [status(thm)], ['11', '42'])).
% 3.52/3.75  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 3.52/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.52/3.75  thf('45', plain, ((v1_funct_1 @ sk_C_1)),
% 3.52/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.52/3.75  thf('46', plain,
% 3.52/3.75      ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C_1)))),
% 3.52/3.75      inference('demod', [status(thm)], ['43', '44', '45'])).
% 3.52/3.75  thf('47', plain,
% 3.52/3.75      (![X0 : $i, X1 : $i]:
% 3.52/3.75         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 3.52/3.75      inference('demod', [status(thm)], ['4', '5'])).
% 3.52/3.75  thf('48', plain,
% 3.52/3.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.52/3.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.52/3.75  thf('49', plain,
% 3.52/3.75      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.52/3.75         ((r1_tarski @ X23 @ X24)
% 3.52/3.75          | ~ (r1_tarski @ (k2_xboole_0 @ X23 @ X25) @ X24))),
% 3.52/3.75      inference('cnf', [status(esa)], [t11_xboole_1])).
% 3.52/3.75  thf('50', plain,
% 3.52/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.52/3.75         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 3.52/3.75      inference('sup-', [status(thm)], ['48', '49'])).
% 3.52/3.75  thf('51', plain,
% 3.52/3.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.52/3.75         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 3.52/3.75      inference('sup-', [status(thm)], ['47', '50'])).
% 3.52/3.75  thf('52', plain,
% 3.52/3.75      (![X0 : $i]:
% 3.52/3.75         (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ 
% 3.52/3.75          (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C_1)))),
% 3.52/3.75      inference('sup-', [status(thm)], ['46', '51'])).
% 3.52/3.75  thf(t44_xboole_1, axiom,
% 3.52/3.75    (![A:$i,B:$i,C:$i]:
% 3.52/3.75     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.52/3.75       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.52/3.75  thf('53', plain,
% 3.52/3.75      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.52/3.75         ((r1_tarski @ X36 @ (k2_xboole_0 @ X37 @ X38))
% 3.52/3.75          | ~ (r1_tarski @ (k4_xboole_0 @ X36 @ X37) @ X38))),
% 3.52/3.75      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.52/3.75  thf('54', plain,
% 3.52/3.75      (![X0 : $i]:
% 3.52/3.75         (r1_tarski @ sk_A @ 
% 3.52/3.75          (k2_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C_1))))),
% 3.52/3.75      inference('sup-', [status(thm)], ['52', '53'])).
% 3.52/3.75  thf('55', plain, ((r1_tarski @ sk_A @ sk_B)),
% 3.52/3.75      inference('sup+', [status(thm)], ['7', '54'])).
% 3.52/3.75  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 3.52/3.75  
% 3.52/3.75  % SZS output end Refutation
% 3.52/3.75  
% 3.52/3.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
