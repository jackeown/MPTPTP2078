%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F1aTkgaeDO

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:24 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 115 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   19
%              Number of atoms          :  514 ( 778 expanded)
%              Number of equality atoms :   42 (  53 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t2_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
           => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_tex_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_zfmisc_1 @ X28 )
      | ( X29 = X28 )
      | ~ ( r1_tarski @ X29 @ X28 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_zfmisc_1 @ X28 )
      | ( X29 = X28 )
      | ~ ( r1_tarski @ X29 @ X28 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','30'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ( ( k3_xboole_0 @ X7 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_tarski @ X22 @ X23 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ sk_A )
      | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','38'])).

thf('40',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('41',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
        = X0 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('49',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ( ( k3_xboole_0 @ X7 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_tarski @ X22 @ X23 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('61',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('simplify_reflect+',[status(thm)],['47','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F1aTkgaeDO
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:31:46 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 400 iterations in 0.273s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.54/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.73  thf(t2_tex_2, conjecture,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.54/0.73       ( ![B:$i]:
% 0.54/0.73         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.54/0.73           ( r1_tarski @ A @ B ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i]:
% 0.54/0.73        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.54/0.73          ( ![B:$i]:
% 0.54/0.73            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.54/0.73              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.54/0.73  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(t36_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.54/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.54/0.73  thf(t1_tex_2, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.73       ( ![B:$i]:
% 0.54/0.73         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.54/0.73           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.54/0.73  thf('2', plain,
% 0.54/0.73      (![X28 : $i, X29 : $i]:
% 0.54/0.73         ((v1_xboole_0 @ X28)
% 0.54/0.73          | ~ (v1_zfmisc_1 @ X28)
% 0.54/0.73          | ((X29) = (X28))
% 0.54/0.73          | ~ (r1_tarski @ X29 @ X28)
% 0.54/0.73          | (v1_xboole_0 @ X29))),
% 0.54/0.73      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((v1_xboole_0 @ (k4_xboole_0 @ X0 @ X1))
% 0.54/0.73          | ((k4_xboole_0 @ X0 @ X1) = (X0))
% 0.54/0.73          | ~ (v1_zfmisc_1 @ X0)
% 0.54/0.73          | (v1_xboole_0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.73  thf(d3_tarski, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.73  thf('4', plain,
% 0.54/0.73      (![X4 : $i, X6 : $i]:
% 0.54/0.73         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf(d1_xboole_0, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.73  thf('7', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.73  thf(d10_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      (![X10 : $i, X12 : $i]:
% 0.54/0.73         (((X10) = (X12))
% 0.54/0.73          | ~ (r1_tarski @ X12 @ X10)
% 0.54/0.73          | ~ (r1_tarski @ X10 @ X12))),
% 0.54/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.73  thf('9', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['6', '9'])).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((v1_xboole_0 @ X1)
% 0.54/0.73          | ~ (v1_zfmisc_1 @ X1)
% 0.54/0.73          | ((k4_xboole_0 @ X1 @ X0) = (X1))
% 0.54/0.73          | ~ (v1_xboole_0 @ X2)
% 0.54/0.73          | ((k4_xboole_0 @ X1 @ X0) = (X2)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['3', '10'])).
% 0.54/0.73  thf(t48_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X19 : $i, X20 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.54/0.73           = (k3_xboole_0 @ X19 @ X20))),
% 0.54/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.54/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.54/0.73  thf('14', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.54/0.73      inference('sup+', [status(thm)], ['12', '13'])).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (![X28 : $i, X29 : $i]:
% 0.54/0.73         ((v1_xboole_0 @ X28)
% 0.54/0.73          | ~ (v1_zfmisc_1 @ X28)
% 0.54/0.73          | ((X29) = (X28))
% 0.54/0.73          | ~ (r1_tarski @ X29 @ X28)
% 0.54/0.73          | (v1_xboole_0 @ X29))),
% 0.54/0.73      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.54/0.73  thf('16', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1))
% 0.54/0.73          | ((k3_xboole_0 @ X0 @ X1) = (X0))
% 0.54/0.73          | ~ (v1_zfmisc_1 @ X0)
% 0.54/0.73          | (v1_xboole_0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.73  thf('17', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      (((v1_xboole_0 @ sk_A)
% 0.54/0.73        | ~ (v1_zfmisc_1 @ sk_A)
% 0.54/0.73        | ((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.54/0.73  thf('19', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.54/0.73  thf('21', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('22', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.54/0.73      inference('clc', [status(thm)], ['20', '21'])).
% 0.54/0.73  thf('23', plain,
% 0.54/0.73      (![X19 : $i, X20 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.54/0.73           = (k3_xboole_0 @ X19 @ X20))),
% 0.54/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      (![X19 : $i, X20 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.54/0.73           = (k3_xboole_0 @ X19 @ X20))),
% 0.54/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.54/0.73           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['23', '24'])).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (((k4_xboole_0 @ sk_A @ sk_A)
% 0.54/0.73         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['22', '25'])).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.54/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.73  thf('28', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.54/0.73      inference('simplify', [status(thm)], ['27'])).
% 0.54/0.73  thf(l32_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.73  thf('29', plain,
% 0.54/0.73      (![X13 : $i, X15 : $i]:
% 0.54/0.73         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.54/0.73          | ~ (r1_tarski @ X13 @ X15))),
% 0.54/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.73  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.73  thf('31', plain,
% 0.54/0.73      (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1)))),
% 0.54/0.73      inference('demod', [status(thm)], ['26', '30'])).
% 0.54/0.73  thf(d7_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.54/0.73       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.73  thf('32', plain,
% 0.54/0.73      (![X7 : $i, X9 : $i]:
% 0.54/0.73         ((r1_xboole_0 @ X7 @ X9) | ((k3_xboole_0 @ X7 @ X9) != (k1_xboole_0)))),
% 0.54/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.54/0.73  thf('33', plain,
% 0.54/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.73        | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['31', '32'])).
% 0.54/0.73  thf('34', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.54/0.73      inference('simplify', [status(thm)], ['33'])).
% 0.54/0.73  thf(t69_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.73       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.54/0.73  thf('35', plain,
% 0.54/0.73      (![X22 : $i, X23 : $i]:
% 0.54/0.73         (~ (r1_xboole_0 @ X22 @ X23)
% 0.54/0.73          | ~ (r1_tarski @ X22 @ X23)
% 0.54/0.73          | (v1_xboole_0 @ X22))),
% 0.54/0.73      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.54/0.73  thf('36', plain,
% 0.54/0.73      (((v1_xboole_0 @ sk_A)
% 0.54/0.73        | ~ (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['34', '35'])).
% 0.54/0.73  thf('37', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('38', plain, (~ (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.54/0.73      inference('clc', [status(thm)], ['36', '37'])).
% 0.54/0.73  thf('39', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (r1_tarski @ sk_A @ sk_A)
% 0.54/0.73          | ((k4_xboole_0 @ sk_A @ sk_B_1) = (X0))
% 0.54/0.73          | ~ (v1_xboole_0 @ X0)
% 0.54/0.73          | ~ (v1_zfmisc_1 @ sk_A)
% 0.54/0.73          | (v1_xboole_0 @ sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['11', '38'])).
% 0.54/0.73  thf('40', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.54/0.73      inference('simplify', [status(thm)], ['27'])).
% 0.54/0.73  thf('41', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('42', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (((k4_xboole_0 @ sk_A @ sk_B_1) = (X0))
% 0.54/0.73          | ~ (v1_xboole_0 @ X0)
% 0.54/0.73          | (v1_xboole_0 @ sk_A))),
% 0.54/0.73      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.54/0.73  thf('43', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('44', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (v1_xboole_0 @ X0) | ((k4_xboole_0 @ sk_A @ sk_B_1) = (X0)))),
% 0.54/0.73      inference('clc', [status(thm)], ['42', '43'])).
% 0.54/0.73  thf('45', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i]:
% 0.54/0.73         ((r1_tarski @ X13 @ X14)
% 0.54/0.73          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 0.54/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.73  thf('46', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (((X0) != (k1_xboole_0))
% 0.54/0.73          | ~ (v1_xboole_0 @ X0)
% 0.54/0.73          | (r1_tarski @ sk_A @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['44', '45'])).
% 0.54/0.73  thf('47', plain,
% 0.54/0.73      (((r1_tarski @ sk_A @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.54/0.73      inference('simplify', [status(thm)], ['46'])).
% 0.54/0.73  thf('48', plain,
% 0.54/0.73      (![X19 : $i, X20 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.54/0.73           = (k3_xboole_0 @ X19 @ X20))),
% 0.54/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.73  thf(t4_boole, axiom,
% 0.54/0.73    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.73  thf('49', plain,
% 0.54/0.73      (![X21 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X21) = (k1_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [t4_boole])).
% 0.54/0.73  thf('50', plain,
% 0.54/0.73      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['48', '49'])).
% 0.54/0.73  thf('51', plain,
% 0.54/0.73      (![X7 : $i, X9 : $i]:
% 0.54/0.73         ((r1_xboole_0 @ X7 @ X9) | ((k3_xboole_0 @ X7 @ X9) != (k1_xboole_0)))),
% 0.54/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.54/0.73  thf('52', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['50', '51'])).
% 0.54/0.73  thf('53', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.54/0.73      inference('simplify', [status(thm)], ['52'])).
% 0.54/0.73  thf('54', plain,
% 0.54/0.73      (![X22 : $i, X23 : $i]:
% 0.54/0.73         (~ (r1_xboole_0 @ X22 @ X23)
% 0.54/0.73          | ~ (r1_tarski @ X22 @ X23)
% 0.54/0.73          | (v1_xboole_0 @ X22))),
% 0.54/0.73      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.54/0.73  thf('55', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.73  thf('56', plain,
% 0.54/0.73      (![X21 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X21) = (k1_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [t4_boole])).
% 0.54/0.73  thf('57', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i]:
% 0.54/0.73         ((r1_tarski @ X13 @ X14)
% 0.54/0.73          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 0.54/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.73  thf('58', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['56', '57'])).
% 0.54/0.73  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.54/0.73      inference('simplify', [status(thm)], ['58'])).
% 0.54/0.73  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.73      inference('demod', [status(thm)], ['55', '59'])).
% 0.54/0.73  thf('61', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.54/0.73      inference('simplify_reflect+', [status(thm)], ['47', '60'])).
% 0.54/0.73  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
