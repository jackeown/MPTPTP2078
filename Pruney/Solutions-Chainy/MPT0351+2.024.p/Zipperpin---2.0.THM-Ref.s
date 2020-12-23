%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LcOo4OaHGb

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 (  95 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  473 ( 588 expanded)
%              Number of equality atoms :   46 (  59 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X55: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X55 ) @ ( k1_zfmisc_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X54: $i] :
      ( ( k2_subset_1 @ X54 )
      = X54 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X55: $i] :
      ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ X58 ) )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ X58 ) )
      | ( ( k4_subset_1 @ X58 @ X57 @ X59 )
        = ( k2_xboole_0 @ X57 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ X52 )
      | ( r2_hidden @ X51 @ X52 )
      | ( v1_xboole_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X56: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X47 @ X46 )
      | ( r1_tarski @ X47 @ X45 )
      | ( X46
       != ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X45: $i,X47: $i] :
      ( ( r1_tarski @ X47 @ X45 )
      | ~ ( r2_hidden @ X47 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['11','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','31'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('34',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['34','39','40'])).

thf('42',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['6','41'])).

thf('43',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X54: $i] :
      ( ( k2_subset_1 @ X54 )
      = X54 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('45',plain,(
    ! [X54: $i] :
      ( ( k2_subset_1 @ X54 )
      = X54 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('46',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LcOo4OaHGb
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 117 iterations in 0.080s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.54  thf(dt_k2_subset_1, axiom,
% 0.20/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (![X55 : $i]: (m1_subset_1 @ (k2_subset_1 @ X55) @ (k1_zfmisc_1 @ X55))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.54  thf('1', plain, (![X54 : $i]: ((k2_subset_1 @ X54) = (X54))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.54  thf('2', plain, (![X55 : $i]: (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X55))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf(t28_subset_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.20/0.54  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ X58))
% 0.20/0.54          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ X58))
% 0.20/0.54          | ((k4_subset_1 @ X58 @ X57 @ X59) = (k2_xboole_0 @ X57 @ X59)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0) = (k2_xboole_0 @ sk_B_1 @ X0))
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.54  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d2_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X51 : $i, X52 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X51 @ X52)
% 0.20/0.54          | (r2_hidden @ X51 @ X52)
% 0.20/0.54          | (v1_xboole_0 @ X52))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.54        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf(fc1_subset_1, axiom,
% 0.20/0.54    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.54  thf('10', plain, (![X56 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X56))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.54  thf('11', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf(d1_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X47 @ X46)
% 0.20/0.54          | (r1_tarski @ X47 @ X45)
% 0.20/0.54          | ((X46) != (k1_zfmisc_1 @ X45)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X45 : $i, X47 : $i]:
% 0.20/0.54         ((r1_tarski @ X47 @ X45) | ~ (r2_hidden @ X47 @ (k1_zfmisc_1 @ X45)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.54  thf('14', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.54  thf(t28_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('16', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf(t100_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X8 @ X9)
% 0.20/0.54           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf(t7_xboole_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.54  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.54  thf('20', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X8 @ X9)
% 0.20/0.54           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf(d5_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.54       ( ![D:$i]:
% 0.20/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.54          | (r2_hidden @ X4 @ X1)
% 0.20/0.54          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.54         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['22', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.54          | ~ (r2_hidden @ X4 @ X2)
% 0.20/0.54          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.54          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.20/0.54          | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.54      inference('clc', [status(thm)], ['25', '29'])).
% 0.20/0.54  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['19', '30'])).
% 0.20/0.54  thf('32', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['18', '31'])).
% 0.20/0.54  thf(t98_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X13 @ X14)
% 0.20/0.54           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf(commutativity_k2_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i]:
% 0.20/0.54         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.54  thf(l51_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X49 : $i, X50 : $i]:
% 0.20/0.54         ((k3_tarski @ (k2_tarski @ X49 @ X50)) = (k2_xboole_0 @ X49 @ X50))),
% 0.20/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X49 : $i, X50 : $i]:
% 0.20/0.54         ((k3_tarski @ (k2_tarski @ X49 @ X50)) = (k2_xboole_0 @ X49 @ X50))),
% 0.20/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.54  thf(t5_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.54  thf('40', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.54  thf('41', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['34', '39', '40'])).
% 0.20/0.54  thf('42', plain, (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) = (sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['6', '41'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k2_subset_1 @ sk_A))
% 0.20/0.54         != (k2_subset_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('44', plain, (![X54 : $i]: ((k2_subset_1 @ X54) = (X54))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.54  thf('45', plain, (![X54 : $i]: ((k2_subset_1 @ X54) = (X54))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.54  thf('46', plain, (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) != (sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.54  thf('47', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['42', '46'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
