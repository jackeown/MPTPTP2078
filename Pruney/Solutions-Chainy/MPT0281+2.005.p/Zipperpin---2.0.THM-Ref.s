%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QQWgrE2GEo

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:47 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   65 (  88 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :   17
%              Number of atoms          :  467 ( 685 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(t82_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) )
        = ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) )
     => ( r3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) )
          = ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) )
       => ( r3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t82_zfmisc_1])).

thf('0',plain,(
    ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X23 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
    = ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( r1_tarski @ X24 @ X22 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('24',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('32',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_B )
    | ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r3_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r3_xboole_0 @ sk_A @ sk_B )
    | ( ( k2_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r3_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    r3_xboole_0 @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QQWgrE2GEo
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % DateTime   : Tue Dec  1 20:24:51 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.70/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.91  % Solved by: fo/fo7.sh
% 0.70/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.91  % done 449 iterations in 0.443s
% 0.70/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.91  % SZS output start Refutation
% 0.70/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.91  thf(r3_xboole_0_type, type, r3_xboole_0: $i > $i > $o).
% 0.70/0.91  thf(t82_zfmisc_1, conjecture,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) =
% 0.70/0.91         ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) =>
% 0.70/0.91       ( r3_xboole_0 @ A @ B ) ))).
% 0.70/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.91    (~( ![A:$i,B:$i]:
% 0.70/0.91        ( ( ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) =
% 0.70/0.91            ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) =>
% 0.70/0.91          ( r3_xboole_0 @ A @ B ) ) )),
% 0.70/0.91    inference('cnf.neg', [status(esa)], [t82_zfmisc_1])).
% 0.70/0.91  thf('0', plain, (~ (r3_xboole_0 @ sk_A @ sk_B)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(d10_xboole_0, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.91  thf('1', plain,
% 0.70/0.91      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.70/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.91  thf('2', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.70/0.91      inference('simplify', [status(thm)], ['1'])).
% 0.70/0.91  thf(d1_zfmisc_1, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.70/0.91       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.70/0.91  thf('3', plain,
% 0.70/0.91      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.70/0.91         (~ (r1_tarski @ X21 @ X22)
% 0.70/0.91          | (r2_hidden @ X21 @ X23)
% 0.70/0.91          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 0.70/0.91      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.70/0.91  thf('4', plain,
% 0.70/0.91      (![X21 : $i, X22 : $i]:
% 0.70/0.91         ((r2_hidden @ X21 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X21 @ X22))),
% 0.70/0.91      inference('simplify', [status(thm)], ['3'])).
% 0.70/0.91  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['2', '4'])).
% 0.70/0.91  thf('6', plain,
% 0.70/0.91      (((k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.70/0.91         = (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['2', '4'])).
% 0.70/0.91  thf(d5_xboole_0, axiom,
% 0.70/0.91    (![A:$i,B:$i,C:$i]:
% 0.70/0.91     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.70/0.91       ( ![D:$i]:
% 0.70/0.91         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.91           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.70/0.91  thf('8', plain,
% 0.70/0.91      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.70/0.91         (~ (r2_hidden @ X2 @ X3)
% 0.70/0.91          | (r2_hidden @ X2 @ X4)
% 0.70/0.91          | (r2_hidden @ X2 @ X5)
% 0.70/0.91          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.70/0.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.70/0.91  thf('9', plain,
% 0.70/0.91      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.70/0.91         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.70/0.91          | (r2_hidden @ X2 @ X4)
% 0.70/0.91          | ~ (r2_hidden @ X2 @ X3))),
% 0.70/0.91      inference('simplify', [status(thm)], ['8'])).
% 0.70/0.91  thf('10', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         ((r2_hidden @ X0 @ X1)
% 0.70/0.91          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['7', '9'])).
% 0.70/0.91  thf('11', plain,
% 0.70/0.91      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.70/0.91         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.70/0.91          | (r2_hidden @ X2 @ X4)
% 0.70/0.91          | ~ (r2_hidden @ X2 @ X3))),
% 0.70/0.91      inference('simplify', [status(thm)], ['8'])).
% 0.70/0.91  thf('12', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.91         ((r2_hidden @ X1 @ X0)
% 0.70/0.91          | (r2_hidden @ X1 @ X2)
% 0.70/0.91          | (r2_hidden @ X1 @ 
% 0.70/0.91             (k4_xboole_0 @ (k4_xboole_0 @ (k1_zfmisc_1 @ X1) @ X0) @ X2)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['10', '11'])).
% 0.70/0.91  thf(t41_xboole_1, axiom,
% 0.70/0.91    (![A:$i,B:$i,C:$i]:
% 0.70/0.91     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.91       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.70/0.91  thf('13', plain,
% 0.70/0.91      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.70/0.91         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.70/0.91           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.70/0.91      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.91  thf('14', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.91         ((r2_hidden @ X1 @ X0)
% 0.70/0.91          | (r2_hidden @ X1 @ X2)
% 0.70/0.91          | (r2_hidden @ X1 @ 
% 0.70/0.91             (k4_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k2_xboole_0 @ X0 @ X2))))),
% 0.70/0.91      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.91  thf('15', plain,
% 0.70/0.91      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.70/0.91         (~ (r2_hidden @ X6 @ X5)
% 0.70/0.91          | ~ (r2_hidden @ X6 @ X4)
% 0.70/0.91          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.70/0.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.70/0.91  thf('16', plain,
% 0.70/0.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.70/0.91         (~ (r2_hidden @ X6 @ X4)
% 0.70/0.91          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.70/0.91      inference('simplify', [status(thm)], ['15'])).
% 0.70/0.91  thf('17', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.91         ((r2_hidden @ X2 @ X0)
% 0.70/0.91          | (r2_hidden @ X2 @ X1)
% 0.70/0.91          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['14', '16'])).
% 0.70/0.91  thf('18', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))
% 0.70/0.91          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.70/0.91          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['6', '17'])).
% 0.70/0.91  thf('19', plain,
% 0.70/0.91      (((r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))
% 0.70/0.91        | (r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['5', '18'])).
% 0.70/0.91  thf('20', plain,
% 0.70/0.91      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.70/0.91         (~ (r2_hidden @ X24 @ X23)
% 0.70/0.91          | (r1_tarski @ X24 @ X22)
% 0.70/0.91          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 0.70/0.91      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.70/0.91  thf('21', plain,
% 0.70/0.91      (![X22 : $i, X24 : $i]:
% 0.70/0.91         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 0.70/0.91      inference('simplify', [status(thm)], ['20'])).
% 0.70/0.91  thf('22', plain,
% 0.70/0.91      (((r2_hidden @ (k2_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.70/0.91        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.70/0.91      inference('sup-', [status(thm)], ['19', '21'])).
% 0.70/0.91  thf('23', plain,
% 0.70/0.91      (![X22 : $i, X24 : $i]:
% 0.70/0.91         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 0.70/0.91      inference('simplify', [status(thm)], ['20'])).
% 0.70/0.91  thf('24', plain,
% 0.70/0.91      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.70/0.91        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['22', '23'])).
% 0.70/0.91  thf(commutativity_k2_xboole_0, axiom,
% 0.70/0.91    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.70/0.91  thf('25', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.91      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.91  thf(t7_xboole_1, axiom,
% 0.70/0.91    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.91  thf('26', plain,
% 0.70/0.91      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.70/0.91      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.91  thf('27', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.70/0.91      inference('sup+', [status(thm)], ['25', '26'])).
% 0.70/0.91  thf('28', plain,
% 0.70/0.91      (![X8 : $i, X10 : $i]:
% 0.70/0.91         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.70/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.91  thf('29', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.70/0.91          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['27', '28'])).
% 0.70/0.91  thf('30', plain,
% 0.70/0.91      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 0.70/0.91        | ((k2_xboole_0 @ sk_A @ sk_B) = (sk_B)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['24', '29'])).
% 0.70/0.91  thf('31', plain,
% 0.70/0.91      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.70/0.91      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.91  thf('32', plain,
% 0.70/0.91      (![X8 : $i, X10 : $i]:
% 0.70/0.91         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.70/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.91  thf('33', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.70/0.91          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['31', '32'])).
% 0.70/0.91  thf('34', plain,
% 0.70/0.91      ((((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))
% 0.70/0.91        | ((k2_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['30', '33'])).
% 0.70/0.91  thf('35', plain,
% 0.70/0.91      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.70/0.91      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.91  thf(d9_xboole_0, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( r3_xboole_0 @ A @ B ) <=>
% 0.70/0.91       ( ( r1_tarski @ A @ B ) | ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.91  thf('36', plain,
% 0.70/0.91      (![X12 : $i, X13 : $i]:
% 0.70/0.91         ((r3_xboole_0 @ X12 @ X13) | ~ (r1_tarski @ X12 @ X13))),
% 0.70/0.91      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.70/0.91  thf('37', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: (r3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.70/0.91  thf('38', plain,
% 0.70/0.91      (((r3_xboole_0 @ sk_A @ sk_B) | ((k2_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.70/0.91      inference('sup+', [status(thm)], ['34', '37'])).
% 0.70/0.91  thf('39', plain, (~ (r3_xboole_0 @ sk_A @ sk_B)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('40', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.70/0.91      inference('clc', [status(thm)], ['38', '39'])).
% 0.70/0.91  thf('41', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.91      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.91  thf('42', plain,
% 0.70/0.91      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.70/0.91      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.91  thf('43', plain,
% 0.70/0.91      (![X12 : $i, X13 : $i]:
% 0.70/0.91         ((r3_xboole_0 @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.70/0.91      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.70/0.91  thf('44', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: (r3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)),
% 0.70/0.91      inference('sup-', [status(thm)], ['42', '43'])).
% 0.70/0.91  thf('45', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: (r3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)),
% 0.70/0.91      inference('sup+', [status(thm)], ['41', '44'])).
% 0.70/0.91  thf('46', plain, ((r3_xboole_0 @ sk_A @ sk_B)),
% 0.70/0.91      inference('sup+', [status(thm)], ['40', '45'])).
% 0.70/0.91  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.70/0.91  
% 0.70/0.91  % SZS output end Refutation
% 0.70/0.91  
% 0.70/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
