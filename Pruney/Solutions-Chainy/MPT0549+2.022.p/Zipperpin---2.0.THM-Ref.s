%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oBp67jmfce

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:17 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 135 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   20
%              Number of atoms          :  505 (1072 expanded)
%              Number of equality atoms :   53 ( 109 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 )
      | ( ( k7_relat_1 @ X18 @ X19 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('20',plain,
    ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('21',plain,
    ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('22',plain,
    ( ( k9_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','16','21'])).

thf('23',plain,
    ( ( k9_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('25',plain,(
    ! [X15: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X15 ) @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k8_relat_1 @ k1_xboole_0 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) )
      = ( k7_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k8_relat_1 @ k1_xboole_0 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k7_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k8_relat_1 @ X14 @ X13 )
        = ( k3_xboole_0 @ X13 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X13 ) @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X0 )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('36',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('37',plain,(
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

thf('38',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k7_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X18 @ X19 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['18','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oBp67jmfce
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 77 iterations in 0.035s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.54  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.36/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.54  thf(t151_relat_1, conjecture,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ B ) =>
% 0.36/0.54       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.54         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i]:
% 0.36/0.54        ( ( v1_relat_1 @ B ) =>
% 0.36/0.54          ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.54            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t151_relat_1])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.36/0.54        | ((k9_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.36/0.54         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.36/0.54       ~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.36/0.54        | ((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.36/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.36/0.55      inference('split', [status(esa)], ['3'])).
% 0.36/0.55  thf(t95_relat_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ B ) =>
% 0.36/0.55       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.55         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X18 : $i, X19 : $i]:
% 0.36/0.55         (~ (r1_xboole_0 @ (k1_relat_1 @ X18) @ X19)
% 0.36/0.55          | ((k7_relat_1 @ X18 @ X19) = (k1_xboole_0))
% 0.36/0.55          | ~ (v1_relat_1 @ X18))),
% 0.36/0.55      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (((~ (v1_relat_1 @ sk_B_1)
% 0.36/0.55         | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.36/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.55  thf('7', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.36/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.36/0.55  thf(t148_relat_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ B ) =>
% 0.36/0.55       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X16 : $i, X17 : $i]:
% 0.36/0.55         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.36/0.55          | ~ (v1_relat_1 @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B_1 @ sk_A))
% 0.36/0.55         | ~ (v1_relat_1 @ sk_B_1)))
% 0.36/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf(t60_relat_1, axiom,
% 0.36/0.55    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.36/0.55     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.55  thf('11', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.55  thf('12', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      ((((k1_xboole_0) = (k9_relat_1 @ sk_B_1 @ sk_A)))
% 0.36/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      ((((k9_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.36/0.55         <= (~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('split', [status(esa)], ['0'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.36/0.55         <= (~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.36/0.55             ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.36/0.55       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.36/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.36/0.55  thf('17', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['2', '16'])).
% 0.36/0.55  thf('18', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 0.36/0.55  thf(dt_k7_relat_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X11 : $i, X12 : $i]:
% 0.36/0.55         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.36/0.55         <= ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.55      inference('split', [status(esa)], ['3'])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.36/0.55       ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.36/0.55      inference('split', [status(esa)], ['3'])).
% 0.36/0.55  thf('22', plain, ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['2', '16', '21'])).
% 0.36/0.55  thf('23', plain, (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['20', '22'])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X16 : $i, X17 : $i]:
% 0.36/0.55         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.36/0.55          | ~ (v1_relat_1 @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.36/0.55  thf(t126_relat_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ A ) =>
% 0.36/0.55       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X15 : $i]:
% 0.36/0.55         (((k8_relat_1 @ (k2_relat_1 @ X15) @ X15) = (X15))
% 0.36/0.55          | ~ (v1_relat_1 @ X15))),
% 0.36/0.55      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (((k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ (k7_relat_1 @ X1 @ X0))
% 0.36/0.55            = (k7_relat_1 @ X1 @ X0))
% 0.36/0.55          | ~ (v1_relat_1 @ X1)
% 0.36/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['24', '25'])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X11 : $i, X12 : $i]:
% 0.36/0.55         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (v1_relat_1 @ X1)
% 0.36/0.55          | ((k8_relat_1 @ (k9_relat_1 @ X1 @ X0) @ (k7_relat_1 @ X1 @ X0))
% 0.36/0.55              = (k7_relat_1 @ X1 @ X0)))),
% 0.36/0.55      inference('clc', [status(thm)], ['26', '27'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      ((((k8_relat_1 @ k1_xboole_0 @ (k7_relat_1 @ sk_B_1 @ sk_A))
% 0.36/0.55          = (k7_relat_1 @ sk_B_1 @ sk_A))
% 0.36/0.55        | ~ (v1_relat_1 @ sk_B_1))),
% 0.36/0.55      inference('sup+', [status(thm)], ['23', '28'])).
% 0.36/0.55  thf('30', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (((k8_relat_1 @ k1_xboole_0 @ (k7_relat_1 @ sk_B_1 @ sk_A))
% 0.36/0.55         = (k7_relat_1 @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.55  thf(t113_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X7 : $i, X8 : $i]:
% 0.36/0.55         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.55  thf(t124_relat_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ B ) =>
% 0.36/0.55       ( ( k8_relat_1 @ A @ B ) =
% 0.36/0.55         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i]:
% 0.36/0.55         (((k8_relat_1 @ X14 @ X13)
% 0.36/0.55            = (k3_xboole_0 @ X13 @ (k2_zfmisc_1 @ (k1_relat_1 @ X13) @ X14)))
% 0.36/0.55          | ~ (v1_relat_1 @ X13))),
% 0.36/0.55      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k8_relat_1 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.36/0.55          | ~ (v1_relat_1 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.36/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.36/0.55  thf('36', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.36/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.36/0.55  thf(t7_xboole_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.36/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.55  thf(t4_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.36/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.36/0.55          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['36', '39'])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k8_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.36/0.55          | ~ (v1_relat_1 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['35', '40'])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.36/0.55        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['31', '41'])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      ((~ (v1_relat_1 @ sk_B_1)
% 0.36/0.55        | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['19', '42'])).
% 0.36/0.55  thf('44', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('45', plain, (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['43', '44'])).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      (![X18 : $i, X19 : $i]:
% 0.36/0.55         (((k7_relat_1 @ X18 @ X19) != (k1_xboole_0))
% 0.36/0.55          | (r1_xboole_0 @ (k1_relat_1 @ X18) @ X19)
% 0.36/0.55          | ~ (v1_relat_1 @ X18))),
% 0.36/0.55      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.55        | ~ (v1_relat_1 @ sk_B_1)
% 0.36/0.55        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.55  thf('48', plain, ((v1_relat_1 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('49', plain,
% 0.36/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.55        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.36/0.55  thf('50', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.36/0.55      inference('simplify', [status(thm)], ['49'])).
% 0.36/0.55  thf('51', plain, ($false), inference('demod', [status(thm)], ['18', '50'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
