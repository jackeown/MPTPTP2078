%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NG5ESbp96m

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 130 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  503 (1050 expanded)
%              Number of equality atoms :   50 ( 105 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t151_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k7_relat_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('6',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('10',plain,
    ( ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('12',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_xboole_0
      = ( k9_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','16'])).

thf('18',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('19',plain,
    ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('20',plain,
    ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('21',plain,
    ( ( k9_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','16','20'])).

thf('22',plain,
    ( ( k9_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('24',plain,(
    ! [X20: $i] :
      ( ( ( k3_xboole_0 @ X20 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X20: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k7_relat_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ) ) )
      = ( k7_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('32',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('33',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('37',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X3 ) ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','32','39','40'])).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X21 @ X22 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['18','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NG5ESbp96m
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 342 iterations in 0.098s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.55  thf(t151_relat_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.55         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i]:
% 0.20/0.55        ( ( v1_relat_1 @ B ) =>
% 0.20/0.55          ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.55            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t151_relat_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.20/0.55        | ((k9_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.20/0.55         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.20/0.55       ~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.20/0.55        | ((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.20/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf(t95_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.55         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ (k1_relat_1 @ X21) @ X22)
% 0.20/0.55          | ((k7_relat_1 @ X21 @ X22) = (k1_xboole_0))
% 0.20/0.55          | ~ (v1_relat_1 @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.55         | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.20/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf('7', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.20/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf(t148_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 0.20/0.55          | ~ (v1_relat_1 @ X18))),
% 0.20/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B_1 @ sk_A))
% 0.20/0.55         | ~ (v1_relat_1 @ sk_B_1)))
% 0.20/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf(t60_relat_1, axiom,
% 0.20/0.55    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.55     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.55  thf('11', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.55  thf('12', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      ((((k1_xboole_0) = (k9_relat_1 @ sk_B_1 @ sk_A)))
% 0.20/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      ((((k9_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.20/0.55         <= (~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.55         <= (~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.20/0.55             ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.55       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.20/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.55  thf('17', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['2', '16'])).
% 0.20/0.55  thf('18', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.20/0.55         <= ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.55       ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf('21', plain, ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['2', '16', '20'])).
% 0.20/0.55  thf('22', plain, (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['19', '21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 0.20/0.55          | ~ (v1_relat_1 @ X18))),
% 0.20/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.55  thf(t22_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ( k3_xboole_0 @
% 0.20/0.55           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.20/0.55         ( A ) ) ))).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X20 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X20 @ 
% 0.20/0.55            (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))) = (
% 0.20/0.55            X20))
% 0.20/0.55          | ~ (v1_relat_1 @ X20))),
% 0.20/0.55      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.20/0.55  thf(t12_setfam_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i]:
% 0.20/0.55         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X20 : $i]:
% 0.20/0.55         (((k1_setfam_1 @ 
% 0.20/0.55            (k2_tarski @ X20 @ 
% 0.20/0.55             (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))))
% 0.20/0.55            = (X20))
% 0.20/0.55          | ~ (v1_relat_1 @ X20))),
% 0.20/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k1_setfam_1 @ 
% 0.20/0.55            (k2_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.20/0.55             (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.20/0.55              (k9_relat_1 @ X1 @ X0))))
% 0.20/0.55            = (k7_relat_1 @ X1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['23', '26'])).
% 0.20/0.55  thf(dt_k7_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X1)
% 0.20/0.55          | ((k1_setfam_1 @ 
% 0.20/0.55              (k2_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.20/0.55               (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.20/0.55                (k9_relat_1 @ X1 @ X0))))
% 0.20/0.55              = (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.55      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      ((((k1_setfam_1 @ 
% 0.20/0.55          (k2_tarski @ (k7_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.55           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.55            k1_xboole_0)))
% 0.20/0.55          = (k7_relat_1 @ sk_B_1 @ sk_A))
% 0.20/0.55        | ~ (v1_relat_1 @ sk_B_1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['22', '29'])).
% 0.20/0.55  thf(t113_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i]:
% 0.20/0.55         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.20/0.55          | ((X13) != (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.55  thf('33', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.55  thf(t7_xboole_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.55  thf(t4_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.55          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i]:
% 0.20/0.55         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X3)))
% 0.20/0.55          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))
% 0.20/0.55          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['34', '37'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '38'])).
% 0.20/0.55  thf('40', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('41', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_B_1 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['30', '32', '39', '40'])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i]:
% 0.20/0.55         (((k7_relat_1 @ X21 @ X22) != (k1_xboole_0))
% 0.20/0.55          | (r1_xboole_0 @ (k1_relat_1 @ X21) @ X22)
% 0.20/0.55          | ~ (v1_relat_1 @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.55        | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.55        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.55  thf('44', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.55        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.55  thf('46', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.20/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.55  thf('47', plain, ($false), inference('demod', [status(thm)], ['18', '46'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
