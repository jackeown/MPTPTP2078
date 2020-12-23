%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ESMj7Irh3N

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:14 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 136 expanded)
%              Number of leaves         :   29 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  563 (1161 expanded)
%              Number of equality atoms :   26 (  46 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) )
        = ( k9_relat_1 @ X24 @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t167_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t167_funct_1])).

thf('1',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( r1_xboole_0 @ ( k2_tarski @ X14 @ X16 ) @ X15 )
      | ( r2_hidden @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X28 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X28 @ X26 ) @ X27 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k1_tarski @ X1 ) ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) @ X23 )
      | ~ ( v4_relat_1 @ X21 @ X23 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('22',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ( ( k7_relat_1 @ X29 @ X30 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('30',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X32 ) )
      | ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k2_tarski @ X31 @ X33 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X32 @ X31 ) @ ( k1_funct_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['4','43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ESMj7Irh3N
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:26:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 271 iterations in 0.155s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(t148_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ B ) =>
% 0.36/0.60       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.36/0.60  thf('0', plain,
% 0.36/0.60      (![X24 : $i, X25 : $i]:
% 0.36/0.60         (((k2_relat_1 @ (k7_relat_1 @ X24 @ X25)) = (k9_relat_1 @ X24 @ X25))
% 0.36/0.60          | ~ (v1_relat_1 @ X24))),
% 0.36/0.60      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.36/0.60  thf(t167_funct_1, conjecture,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.60       ( r1_tarski @
% 0.36/0.60         ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.36/0.60         ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i,B:$i]:
% 0.36/0.60        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.60          ( r1_tarski @
% 0.36/0.60            ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.36/0.60            ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t167_funct_1])).
% 0.36/0.60  thf('1', plain,
% 0.36/0.60      (~ (r1_tarski @ 
% 0.36/0.60          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.36/0.60          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      ((~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.36/0.60           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.36/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.60  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.36/0.60          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.60  thf(t69_enumset1, axiom,
% 0.36/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.60  thf('5', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.60  thf(t57_zfmisc_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.36/0.60          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.36/0.60  thf('6', plain,
% 0.36/0.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.60         ((r2_hidden @ X14 @ X15)
% 0.36/0.60          | (r1_xboole_0 @ (k2_tarski @ X14 @ X16) @ X15)
% 0.36/0.60          | (r2_hidden @ X16 @ X15))),
% 0.36/0.60      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.36/0.60          | (r2_hidden @ X0 @ X1)
% 0.36/0.60          | (r2_hidden @ X0 @ X1))),
% 0.36/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.60  thf('8', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.36/0.60      inference('simplify', [status(thm)], ['7'])).
% 0.36/0.60  thf(t207_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ C ) =>
% 0.36/0.60       ( ( r1_xboole_0 @ A @ B ) =>
% 0.36/0.60         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.60  thf('9', plain,
% 0.36/0.60      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.36/0.60         (~ (r1_xboole_0 @ X26 @ X27)
% 0.36/0.60          | ~ (v1_relat_1 @ X28)
% 0.36/0.60          | ((k7_relat_1 @ (k7_relat_1 @ X28 @ X26) @ X27) = (k1_xboole_0)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.36/0.60  thf('10', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((r2_hidden @ X1 @ X0)
% 0.36/0.60          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ (k1_tarski @ X1)) @ X0)
% 0.36/0.60              = (k1_xboole_0))
% 0.36/0.60          | ~ (v1_relat_1 @ X2))),
% 0.36/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.60  thf(d10_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.60      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.60  thf(d18_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ B ) =>
% 0.36/0.60       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.60  thf('13', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i]:
% 0.36/0.60         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.36/0.60          | (v4_relat_1 @ X17 @ X18)
% 0.36/0.60          | ~ (v1_relat_1 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.60  thf(fc23_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 0.36/0.60       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 0.36/0.60         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 0.36/0.60         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 0.36/0.60  thf('15', plain,
% 0.36/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.60         ((v4_relat_1 @ (k7_relat_1 @ X21 @ X22) @ X23)
% 0.36/0.60          | ~ (v4_relat_1 @ X21 @ X23)
% 0.36/0.60          | ~ (v1_relat_1 @ X21))),
% 0.36/0.60      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.36/0.60  thf('16', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X0)
% 0.36/0.60          | ~ (v1_relat_1 @ X0)
% 0.36/0.60          | (v4_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.60  thf('17', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((v4_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.36/0.60          | ~ (v1_relat_1 @ X0))),
% 0.36/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.36/0.60  thf('18', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i]:
% 0.36/0.60         (~ (v4_relat_1 @ X17 @ X18)
% 0.36/0.60          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.36/0.60          | ~ (v1_relat_1 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.36/0.60  thf('19', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X0)
% 0.36/0.60          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.36/0.60          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.36/0.60             (k1_relat_1 @ X0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.60  thf(dt_k7_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.36/0.60  thf('20', plain,
% 0.36/0.60      (![X19 : $i, X20 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k7_relat_1 @ X19 @ X20)))),
% 0.36/0.60      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.36/0.60  thf('21', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.36/0.60           (k1_relat_1 @ X0))
% 0.36/0.60          | ~ (v1_relat_1 @ X0))),
% 0.36/0.60      inference('clc', [status(thm)], ['19', '20'])).
% 0.36/0.60  thf(t97_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ B ) =>
% 0.36/0.60       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.36/0.60         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      (![X29 : $i, X30 : $i]:
% 0.36/0.60         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 0.36/0.60          | ((k7_relat_1 @ X29 @ X30) = (X29))
% 0.36/0.60          | ~ (v1_relat_1 @ X29))),
% 0.36/0.60      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.36/0.60  thf('23', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X0)
% 0.36/0.60          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.36/0.60          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.36/0.60              = (k7_relat_1 @ X0 @ X1)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.60  thf('24', plain,
% 0.36/0.60      (![X19 : $i, X20 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k7_relat_1 @ X19 @ X20)))),
% 0.36/0.60      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.36/0.60  thf('25', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.36/0.60            = (k7_relat_1 @ X0 @ X1))
% 0.36/0.60          | ~ (v1_relat_1 @ X0))),
% 0.36/0.60      inference('clc', [status(thm)], ['23', '24'])).
% 0.36/0.60  thf('26', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0)))
% 0.36/0.60          | ~ (v1_relat_1 @ X1)
% 0.36/0.60          | (r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.36/0.60          | ~ (v1_relat_1 @ X1))),
% 0.36/0.60      inference('sup+', [status(thm)], ['10', '25'])).
% 0.36/0.60  thf('27', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.36/0.60          | ~ (v1_relat_1 @ X1)
% 0.36/0.60          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0))))),
% 0.36/0.60      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.60  thf('28', plain,
% 0.36/0.60      (~ (r1_tarski @ 
% 0.36/0.60          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.36/0.60          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.36/0.60           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.36/0.60        | ~ (v1_relat_1 @ sk_B)
% 0.36/0.60        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.60  thf(t60_relat_1, axiom,
% 0.36/0.60    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.36/0.60     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.60  thf('30', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.60  thf('31', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.36/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.60  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('33', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.36/0.60  thf('34', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.36/0.60  thf(t118_funct_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.60       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.36/0.60           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.36/0.60         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.36/0.60           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.36/0.60  thf('35', plain,
% 0.36/0.60      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X31 @ (k1_relat_1 @ X32))
% 0.36/0.60          | ~ (r2_hidden @ X33 @ (k1_relat_1 @ X32))
% 0.36/0.60          | ((k9_relat_1 @ X32 @ (k2_tarski @ X31 @ X33))
% 0.36/0.60              = (k2_tarski @ (k1_funct_1 @ X32 @ X31) @ 
% 0.36/0.60                 (k1_funct_1 @ X32 @ X33)))
% 0.36/0.60          | ~ (v1_funct_1 @ X32)
% 0.36/0.60          | ~ (v1_relat_1 @ X32))),
% 0.36/0.60      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.36/0.60  thf('36', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ sk_B)
% 0.36/0.60          | ~ (v1_funct_1 @ sk_B)
% 0.36/0.60          | ((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.36/0.60              = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.36/0.60                 (k1_funct_1 @ sk_B @ X0)))
% 0.36/0.60          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.60  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('39', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.36/0.60            = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.36/0.60               (k1_funct_1 @ sk_B @ X0)))
% 0.36/0.60          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.36/0.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.36/0.60  thf('40', plain,
% 0.36/0.60      (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ sk_A))
% 0.36/0.60         = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['33', '39'])).
% 0.36/0.60  thf('41', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.60  thf('42', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.60  thf('43', plain,
% 0.36/0.60      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.36/0.60         = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.36/0.60  thf('44', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.60      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.60  thf('45', plain, ($false),
% 0.36/0.60      inference('demod', [status(thm)], ['4', '43', '44'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
